import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.SplitIfs

/-!
# A combinatorial component of the non-sigma-compactness argument

See verification-status.json for the complete verification record.

Here `none` represents the limit point. The result is a theorem about sequences
of optional natural numbers, not about compactness or the Vietoris topology.
The finite-witness condition is an explicit hypothesis in this file.
TopologyProof.lean derives it from compactness and proves the unconditional
non-sigma-compactness theorem.

This diagonal construction is an alternative to using the Baire category theorem.
-/

namespace VietorisOmegaOne.Diagonal

/-- Put n at position pair n (b n + 1), and put none at every other position. -/
def delayedSequence (b : ℕ → ℕ) (k : ℕ) : Option ℕ :=
  if (Nat.unpair k).2 = b (Nat.unpair k).1 + 1 then
    some (Nat.unpair k).1
  else
    none

theorem at_zero (b : ℕ → ℕ) : delayedSequence b 0 = none := by
  simp [delayedSequence]

theorem at_pair (b : ℕ → ℕ) (n : ℕ) :
    delayedSequence b (Nat.pair n (b n + 1)) = some n := by
  simp [delayedSequence, Nat.unpair_pair]

theorem hit_after_bound (b : ℕ → ℕ) {k n : ℕ}
    (h : delayedSequence b k = some n) : b n < k := by
  unfold delayedSequence at h
  split_ifs at h with hc
  · have hn : (Nat.unpair k).1 = n := Option.some.inj h
    have hk := Nat.unpair_right_le k
    rw [hc, hn] at hk
    omega

theorem surjective (b : ℕ → ℕ) : Function.Surjective (delayedSequence b) := by
  intro x
  cases x with
  | none => exact ⟨0, at_zero b⟩
  | some n => exact ⟨Nat.pair n (b n + 1), at_pair b n⟩

/-- No countable family with the stated finite-witness bounds contains all
surjective sequences whose zeroth coordinate is none. This is NOT the main
topological theorem: the witness-bound premise is a real premise. -/
theorem escapes_bounded_families
    (C : ℕ → Set (ℕ → Option ℕ)) (b : ℕ → ℕ)
    (capture : ∀ n, ∀ f ∈ C n, ∃ k, k ≤ b n ∧ f k = some n) :
    ∃ g : ℕ → Option ℕ,
      g 0 = none ∧ Function.Surjective g ∧ ∀ n, g ∉ C n := by
  refine ⟨delayedSequence b, at_zero b, surjective b, ?_⟩
  intro n hn
  obtain ⟨k, hk, hvalue⟩ := capture n (delayedSequence b) hn
  have hlate := hit_after_bound b hvalue
  omega

end VietorisOmegaOne.Diagonal
