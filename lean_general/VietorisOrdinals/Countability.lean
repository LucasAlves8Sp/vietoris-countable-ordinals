import VietorisOrdinals.Model
noncomputable section
open Set TopologicalSpace
universe u
namespace VietorisOrdinals
variable (X : Type u) [TopologicalSpace X] [SecondCountableTopology X]

def finiteUnion (F : Finset (countableBasis X)) : Set X := ⋃ U ∈ F, (U : Set X)
def smallOpen : Set (Set X) := Set.range (finiteUnion X)
theorem countable_smallOpen : (smallOpen X).Countable := Set.countable_range _
theorem finiteUnion_open (F : Finset (countableBasis X)) : IsOpen (finiteUnion X F) :=
  isOpen_iUnion fun U => isOpen_iUnion fun _ => isOpen_of_mem_countableBasis U.property
theorem smallOpen_open {U : Set X} (hU : U ∈ smallOpen X) : IsOpen U := by
  obtain ⟨F,rfl⟩ := hU
  exact finiteUnion_open X F

def subgenerators : Set (Set (K X)) :=
  (fun U : Set X => {f : K X | Set.range f.val ⊆ U}) '' smallOpen X ∪
  ⋃ i : ℕ, (fun U : Set X => {f : K X | f.val i ∈ U}) '' countableBasis X
def smallTopology : TopologicalSpace (K X) := generateFrom (subgenerators X)
theorem countable_subgenerators : (subgenerators X).Countable :=
  ((countable_smallOpen X).image _).union
    (Set.countable_iUnion fun _ => (countable_countableBasis X).image _)
theorem small_open_tube {U : Set X} (hU : U ∈ smallOpen X) :
    @IsOpen (K X) (smallTopology X) {f : K X | Set.range f.val ⊆ U} :=
  isOpen_generateFrom_of_mem (Or.inl ⟨U,hU,rfl⟩)
theorem small_open_coordinate (i : ℕ) {U : Set X} (hU : U ∈ countableBasis X) :
    @IsOpen (K X) (smallTopology X) {f : K X | f.val i ∈ U} :=
  isOpen_generateFrom_of_mem (Or.inr (Set.mem_iUnion.mpr ⟨i,U,hU,rfl⟩))

theorem compact_refinement {C U : Set X} (hc : IsCompact C)
    (ho : IsOpen U) (hcu : C ⊆ U) :
    ∃ W ∈ smallOpen X, C ⊆ W ∧ W ⊆ U := by
  classical
  let B := {B : countableBasis X // (B : Set X) ⊆ U}
  obtain ⟨F,hF⟩ := hc.elim_finite_subcover (fun B : B => (B.val : Set X))
    (fun B => isOpen_of_mem_countableBasis B.val.property) (by
      intro x hx
      obtain ⟨V,hV,hxV,hVU⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open (hcu hx) ho
      exact Set.mem_iUnion.mpr ⟨⟨⟨V,hV⟩,hVU⟩,hxV⟩)
  refine ⟨finiteUnion X (F.image Subtype.val), ⟨_,rfl⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨B,hB⟩ := Set.mem_iUnion.mp (hF hx)
    obtain ⟨hBF,hxB⟩ := Set.mem_iUnion.mp hB
    exact Set.mem_iUnion.mpr ⟨B.val,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨B,hBF,rfl⟩,hxB⟩⟩
  · intro x hx
    obtain ⟨B,hB⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hBF,hxB⟩ := Set.mem_iUnion.mp hB
    obtain ⟨D,hD,he⟩ := Finset.mem_image.mp hBF
    exact D.property (he.symm ▸ hxB)

theorem small_open_any_tube {U : Set X} (ho : IsOpen U) :
    @IsOpen (K X) (smallTopology X) {f : K X | Set.range f.val ⊆ U} := by
  letI : TopologicalSpace (K X) := smallTopology X
  apply isOpen_iff_mem_nhds.mpr
  intro f hf
  obtain ⟨W,hW,hfW,hWU⟩ := compact_refinement X f.property ho hf
  exact Filter.mem_of_superset ((small_open_tube X hW).mem_nhds hfW)
    (fun g hg => hg.trans hWU)

theorem small_open_any_coordinate (i : ℕ) {U : Set X} (ho : IsOpen U) :
    @IsOpen (K X) (smallTopology X) {f : K X | f.val i ∈ U} := by
  letI : TopologicalSpace (K X) := smallTopology X
  apply isOpen_iff_mem_nhds.mpr
  intro f hf
  obtain ⟨V,hV,hfV,hVU⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hf ho
  exact Filter.mem_of_superset ((small_open_coordinate X i hV).mem_nhds hfV)
    (fun g hg => hVU hg)

theorem topology_eq_small : kTopology X = smallTopology X := by
  apply le_antisymm
  · apply le_generateFrom
    intro A hA
    rcases hA with hA | hA
    · obtain ⟨U,hU,rfl⟩ := hA
      exact open_tube X U (smallOpen_open X hU)
    · obtain ⟨i,U,hU,rfl⟩ := Set.mem_iUnion.mp hA
      exact open_coordinate X i U (isOpen_of_mem_countableBasis hU)
  · change smallTopology X ≤ TopologicalSpace.induced (fun f : K X => f.val) (powerTopology X)
    letI : TopologicalSpace (K X) := smallTopology X
    apply le_induced_generateFrom
    rintro A ⟨U,F,V,hU,hV,rfl⟩
    have he : (fun f : K X => f.val) ⁻¹' basic X U F V =
        {f : K X | Set.range f.val ⊆ U} ∩ ⋂ i ∈ F, {f : K X | f.val i ∈ V i} := by
      ext f; simp [basic]
    rw [he]
    exact (small_open_any_tube X hU).inter
      (isOpen_biInter_finset fun i hi => small_open_any_coordinate X i (hV i hi))

theorem second_countable : SecondCountableTopology (K X) := by
  rw [topology_eq_small X]
  exact SecondCountableTopology.mk' (countable_subgenerators X)
theorem lindelof : IsLindelof (Set.univ : Set (K X)) := by
  letI := second_countable X
  exact isLindelof_univ
end VietorisOrdinals
