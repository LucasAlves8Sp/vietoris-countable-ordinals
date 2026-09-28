$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
$elanBin = Join-Path $env:USERPROFILE '.elan/bin'
if (Test-Path -LiteralPath $elanBin) { $env:PATH = $elanBin + ';' + $env:PATH }
if (-not (Get-Command lake -CommandType Application -ErrorAction SilentlyContinue)) {
    throw 'Lean/lake not found. Install the version pinned in lean-toolchain.'
}
& lake env lean --version
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
$modules = @('VietorisOrdinals/Model','VietorisOrdinals/Diagonal',
    'VietorisOrdinals/Countability','VietorisOrdinals/Obstruction',
    'VietorisOrdinals/Menger','VietorisOrdinals/Ordinals',
    'VietorisOrdinals/Results','VietorisOrdinals')
foreach ($module in $modules) {
    $outputFile = Join-Path '.lake/build/lib/lean' ($module + '.olean')
    New-Item -ItemType Directory -Force -Path (Split-Path $outputFile) | Out-Null
    Write-Output ('Checking ' + $module + '.lean')
    & lake env lean -j1 ($module + '.lean') -o $outputFile
    if ($LASTEXITCODE -ne 0) { throw ('Compilation failed: ' + $module) }
}
$auditOutput = @(& lake env lean -j1 FullAudit.lean 2>&1)
$auditExit = $LASTEXITCODE
$auditOutput | ForEach-Object { Write-Output $_ }
if ($auditExit -ne 0) { throw 'Full theorem audit failed.' }
$auditText = $auditOutput -join "`n"
$targets = @('second_countable','not_sigmaCompact','not_menger','ordinal_main','ordinal_full','ordinal_subsets_countable')
$allowed = @('propext','Classical.choice','Quot.sound')
foreach ($target in $targets) {
    $match = [regex]::Match($auditText, "VietorisOrdinals\.$target'? depends on axioms:\s*\[([^\]]*)\]")
    if (-not $match.Success) { throw ('Missing axiom report: ' + $target) }
    foreach ($reported in ($match.Groups[1].Value.Split(',') | ForEach-Object { $_.Trim() } | Where-Object { $_ })) {
        if ($reported -notin $allowed) { throw ('Unexpected axiom: ' + $reported) }
    }
}
Write-Output 'VERIFIED: all requested declarations compiled and their transitive axiom reports passed.'
Write-Output 'See README.md and verification-status.json for the precise scope and recorded source hashes.'
