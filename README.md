# Compact-range Vietoris powers of countable ordinals

**Lucas Alves de Almeida** · lucasdeirva8x@gmail.com

For every ordinal **omega < alpha < omega one**, the space **K(alpha, ord)** is **second-countable and Lindelof, but neither sigma-compact nor Menger**.

This manuscript and Lean 4 project address the full stated interval in Question 1, page 11, of Christopher Caruvana and Jared Holshouser, *An Adaptation of the Vietoris Topology for Ordered Compact Sets*, [arXiv:2507.17936v3](https://arxiv.org/abs/2507.17936v3).

## Read the result

- [Revised article (PDF)](paper/paper.pdf)
- [Local Lean verification record (PDF)](paper/lean-verification-record.pdf)
- [Earlier omega + 1 manuscript (PDF)](paper/earlier-convergent-sequence-paper.pdf)
- [Exact formal scope and reproduction instructions](lean_general/README.md)
- [Principal Lean declaration](lean_general/VietorisOrdinals/Results.lean)
- [Successful transitive axiom audit](lean_general/verification-audit.log)
- [Machine-readable verification status and source hashes](lean_general/verification-status.json)

## Why the interval follows from the first case

The revised paper makes the closed-subspace transfer central (Proposition 4.1; Proposition 5.1 in the earlier draft). At a fixed index omega, a closed inclusion A into X induces a closed embedding of K(A, ord, omega) into K(X, ord, omega).

For every ordinal in the stated interval, [0, omega] is closed and homeomorphic to omega + 1, and both default indexing cardinals equal omega. The earlier non-sigma-compactness theorem therefore transfers immediately, because closed subspaces of sigma-compact spaces are sigma-compact. A general countable-base theorem gives Lindelofness. The self-contained delayed diagonal is retained as a second proof and yields failure of the Menger property.

The earlier project is [vietoris-omega-one](https://github.com/LucasAlves8Sp/vietoris-omega-one).

## Lean verification

The principal declaration is `VietorisOrdinals.ordinal_full`. It quantifies over actual mathlib ordinals and has only the two inequalities `omega < a` and `a < omega one` as mathematical hypotheses. The formal carrier consists of maps from the natural numbers with genuinely compact image, with the source's range-plus-finite-coordinate topology.

The recorded successful check used **Lean 4.19.0** (commit `6caaee842e94`) and **mathlib v4.19.0**, pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All six audited declarations report only `propext`, `Classical.choice`, and `Quot.sound`. No admitted proof, custom assumed mathematical result, or native-computation trust axiom occurs in those declarations.

The Lean proof follows the self-contained diagonal argument. The abstract closed-subspace transfer proposition has a mathematical proof in the article; it is not a separately formalized theorem in this package. The editorial revision preserves the previously verified Lean sources and their hashes. The uncountable classification is attributed to the reference and lies outside this formalization.

After installing the pinned Lean toolchain, run from `lean_general`:

```powershell
lake exe cache get
.\verify.ps1
```

On other systems, run `lake build` and then `lake env lean FullAudit.lean`; check successful exit and all printed axiom lists. Keep the supplied dependency lockfile. Individual compiler logs, exact theorem types, source definitions and checksums are included; installed toolchains, dependencies and compiled libraries are omitted.

`FILES.sha256` identifies all uploaded repository files other than itself. The formalization's original manifests remain inside `lean_general`.

This is a reproducible local verification record, not an institutional certificate, independent peer review, or a publication-priority claim. The correspondence with the source definitions and indexing convention is explicit in the manuscript.

## AI disclosure

Lucas Alves de Almeida proposed and guided the generalization of his earlier result, directed the investigation toward the delayed diagonal method, and requested the central closed-subspace presentation. ChatGPT-Astra developed the main general argument and performed the primary mathematical development, Lean formalization, verification work and manuscript preparation under his direction.
