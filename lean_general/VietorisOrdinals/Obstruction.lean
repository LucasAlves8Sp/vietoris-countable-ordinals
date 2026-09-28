import VietorisOrdinals.Model
import VietorisOrdinals.Diagonal
noncomputable section
open Set TopologicalSpace
universe u
namespace VietorisOrdinals
variable (X : Type u) [TopologicalSpace X] [T2Space X]
variable (q : Option ℕ → X)

def surjectionSet : Set (K X) :=
  {f | f.val 0 = q none ∧ Set.range f.val = Set.range q}

theorem closed_surjections (hc : IsCompact (Set.range q)) :
    IsClosed (surjectionSet X q) := by
  have hhit (x : X) : IsClosed {f : K X | x ∈ Set.range f.val} := by
    have ho := open_tube X ({x}ᶜ) isClosed_singleton.isOpen_compl
    have he : {f : K X | Set.range f.val ⊆ {x}ᶜ} =
        {f : K X | x ∈ Set.range f.val}ᶜ := by
      ext f
      simp only [Set.mem_setOf_eq,Set.mem_compl_iff,Set.subset_def,Set.mem_singleton_iff]
      constructor
      · intro h hx; exact h x hx rfl
      · intro h y hy hyx; exact h (hyx ▸ hy)
    rw [he] at ho
    exact isOpen_compl_iff.mp ho
  have he : surjectionSet X q =
      {f : K X | f.val 0 = q none} ∩
      ((⋂ k : ℕ, {f : K X | f.val k ∈ Set.range q}) ∩
      ⋂ a : Option ℕ, {f : K X | q a ∈ Set.range f.val}) := by
    ext f
    simp only [surjectionSet,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    constructor
    · rintro ⟨hz,hr⟩
      exact ⟨hz,⟨fun k => hr ▸ Set.mem_range_self k,fun a => hr.symm ▸ Set.mem_range_self a⟩⟩
    · rintro ⟨hz,hsub,hsup⟩
      refine ⟨hz,Set.Subset.antisymm ?_ ?_⟩
      · rintro x ⟨k,rfl⟩; exact hsub k
      · rintro x ⟨a,rfl⟩; exact hsup a
  rw [he]
  exact (isClosed_singleton.preimage (continuous_coordinate X 0)).inter
    ((isClosed_iInter fun k => hc.isClosed.preimage (continuous_coordinate X k)).inter
      (isClosed_iInter fun a => hhit (q a)))

theorem compact_occurrence_bound
    (ho : ∀ n : ℕ, IsOpen ({q (some n)} : Set X))
    (C : Set (K X)) (hc : IsCompact C)
    (hs : C ⊆ surjectionSet X q) (n : ℕ) :
    ∃ b : ℕ, ∀ f ∈ C, ∃ k ≤ b, f.val k = q (some n) := by
  have hopen (k : ℕ) : IsOpen {f : K X | f.val k = q (some n)} :=
    (continuous_coordinate X k).isOpen_preimage _ (ho n)
  obtain ⟨J,hJ⟩ := hc.elim_finite_subcover
    (fun k => {f : K X | f.val k = q (some n)}) hopen (by
      intro f hf
      have hmem : q (some n) ∈ Set.range f.val := (hs hf).2.symm ▸ Set.mem_range_self (some n)
      obtain ⟨k,hk⟩ := hmem
      exact Set.mem_iUnion.mpr ⟨k,hk⟩)
  refine ⟨J.sup id,?_⟩
  intro f hf
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hJ hf)
  obtain ⟨hkJ,he⟩ := Set.mem_iUnion.mp hk
  exact ⟨k,Finset.le_sup (f := id) hkJ,he⟩

theorem delayed_range (b : ℕ → ℕ) :
    Set.range (q ∘ VietorisOmegaOne.Diagonal.delayedSequence b) = Set.range q := by
  rw [Set.range_comp,Set.range_eq_univ.mpr (VietorisOmegaOne.Diagonal.surjective b),Set.image_univ]

theorem not_sigmaCompact
    (hq : Function.Injective q) (hc : IsCompact (Set.range q))
    (ho : ∀ n : ℕ, IsOpen ({q (some n)} : Set X)) :
    ¬ IsSigmaCompact (Set.univ : Set (K X)) := by
  intro h
  obtain ⟨C,hC,hcover⟩ := h.of_isClosed_subset (closed_surjections X q hc) (Set.subset_univ _)
  have hsub (n : ℕ) : C n ⊆ surjectionSet X q := by
    rw [← hcover]; exact Set.subset_iUnion C n
  choose b hb using fun n => compact_occurrence_bound X q ho (C n) (hC n) (hsub n) n
  let g : K X := ⟨q ∘ VietorisOmegaOne.Diagonal.delayedSequence b, by
    rw [delayed_range X q b]; exact hc⟩
  have hg : g ∈ surjectionSet X q := by
    refine ⟨?_,delayed_range X q b⟩
    change q (VietorisOmegaOne.Diagonal.delayedSequence b 0) = q none
    rw [VietorisOmegaOne.Diagonal.at_zero]
  rw [← hcover] at hg
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  obtain ⟨k,hk,he⟩ := hb n g hn
  have he' : VietorisOmegaOne.Diagonal.delayedSequence b k = some n := hq he
  exact (Nat.not_lt_of_ge hk) (VietorisOmegaOne.Diagonal.hit_after_bound b he')
end VietorisOrdinals
