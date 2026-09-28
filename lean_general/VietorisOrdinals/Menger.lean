import VietorisOrdinals.Obstruction
noncomputable section
open Set TopologicalSpace
universe u
namespace VietorisOrdinals

/-- The usual Menger open-cover selection property, stated without a
restriction on the cardinalities of the covers. -/
def Menger (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ U : ℕ → Set (Set Y),
    (∀ n, ∀ s ∈ U n, IsOpen s) →
    (∀ n, ∀ x : Y, ∃ s ∈ U n, x ∈ s) →
    ∃ F : ℕ → Finset (Set Y),
      (∀ n, ∀ s ∈ F n, s ∈ U n) ∧
      ∀ x : Y, ∃ n, ∃ s ∈ F n, x ∈ s

variable (X : Type u) [TopologicalSpace X] [T2Space X]
variable (q : Option ℕ → X)

def badCover (n m : ℕ) : Set (K X) :=
  (surjectionSet X q)ᶜ ∪ {f : K X | ∃ k ≤ m, f.val k = q (some n)}

theorem badCover_open (hc : IsCompact (Set.range q))
    (ho : ∀ n : ℕ, IsOpen ({q (some n)} : Set X)) (n m : ℕ) :
    IsOpen (badCover X q n m) := by
  have he : {f : K X | ∃ k ≤ m, f.val k = q (some n)} =
      ⋃ k : ℕ, ⋃ (_ : k ≤ m), {f : K X | f.val k = q (some n)} := by
    ext f; simp
  unfold badCover
  rw [he]
  exact (closed_surjections X q hc).isOpen_compl.union
    (isOpen_iUnion fun k => isOpen_iUnion fun _ =>
      (continuous_coordinate X k).isOpen_preimage _ (ho n))

theorem badCover_covers (n : ℕ) (f : K X) : ∃ m, f ∈ badCover X q n m := by
  by_cases hf : f ∈ surjectionSet X q
  · have hmem : q (some n) ∈ Set.range f.val := hf.2.symm ▸ Set.mem_range_self (some n)
    obtain ⟨k,hk⟩ := hmem
    exact ⟨k,Or.inr ⟨k,le_rfl,hk⟩⟩
  · exact ⟨0,Or.inl hf⟩

theorem badCover_escapes (hq : Function.Injective q) (hc : IsCompact (Set.range q))
    (F : ℕ → Finset ℕ) : ∃ g : K X, ∀ n, ∀ m ∈ F n, g ∉ badCover X q n m := by
  let b : ℕ → ℕ := fun n => (F n).sup id
  let g : K X := ⟨q ∘ VietorisOmegaOne.Diagonal.delayedSequence b, by
    rw [delayed_range X q b]; exact hc⟩
  have hg : g ∈ surjectionSet X q := by
    refine ⟨?_,delayed_range X q b⟩
    change q (VietorisOmegaOne.Diagonal.delayedSequence b 0) = q none
    rw [VietorisOmegaOne.Diagonal.at_zero]
  refine ⟨g,?_⟩
  intro n m hm h
  rcases h with h | ⟨k,hkm,hk⟩
  · exact h hg
  · have hmb : m ≤ b n := Finset.le_sup (f := id) hm
    have hlate := VietorisOmegaOne.Diagonal.hit_after_bound b (hq hk)
    exact (Nat.not_lt_of_ge (hkm.trans hmb)) hlate

theorem not_menger (hq : Function.Injective q) (hc : IsCompact (Set.range q))
    (ho : ∀ n : ℕ, IsOpen ({q (some n)} : Set X)) : ¬ Menger (K X) := by
  classical
  intro h
  obtain ⟨F,hF,hcover⟩ := h (fun n => Set.range (badCover X q n))
    (by rintro n s ⟨m,rfl⟩; exact badCover_open X q hc ho n m)
    (by
      intro n f
      obtain ⟨m,hm⟩ := badCover_covers X q n f
      exact ⟨badCover X q n m,Set.mem_range_self _,hm⟩)
  let idx (n : ℕ) (s : Set (K X)) : ℕ :=
    if hs : s ∈ F n then Classical.choose (hF n s hs) else 0
  have hidx (n : ℕ) (s : Set (K X)) (hs : s ∈ F n) :
      badCover X q n (idx n s) = s := by
    simp only [idx,dif_pos hs]
    exact Classical.choose_spec (hF n s hs)
  obtain ⟨g,hg⟩ := badCover_escapes X q hq hc (fun n => (F n).image (idx n))
  obtain ⟨n,s,hs,hgs⟩ := hcover g
  apply hg n (idx n s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
  rwa [hidx n s hs]
end VietorisOrdinals
