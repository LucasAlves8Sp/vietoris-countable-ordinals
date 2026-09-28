import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Compact
import Mathlib.SetTheory.Cardinal.Aleph

/-! The countable compact-range Vietoris power, using the basic sets of
Caruvana--Holshouser, Definitions 1.8 and 1.14. -/
noncomputable section
open Set TopologicalSpace
universe u
namespace VietorisOrdinals
variable (X : Type u) [TopologicalSpace X]

def basic (U : Set X) (F : Finset ℕ) (V : ℕ → Set X) : Set (ℕ → X) :=
  {f | Set.range f ⊆ U ∧ ∀ i ∈ F, f i ∈ V i}
def generators : Set (Set (ℕ → X)) :=
  {A | ∃ (U : Set X) (F : Finset ℕ) (V : ℕ → Set X),
    IsOpen U ∧ (∀ i ∈ F, IsOpen (V i)) ∧ A = basic X U F V}
def powerTopology : TopologicalSpace (ℕ → X) := generateFrom (generators X)
def K := {f : ℕ → X // IsCompact (Set.range f)}
instance kTopology : TopologicalSpace (K X) :=
  TopologicalSpace.induced (fun f : K X => f.val) (powerTopology X)

theorem open_basic (U : Set X) (F : Finset ℕ) (V : ℕ → Set X)
    (hU : IsOpen U) (hV : ∀ i ∈ F, IsOpen (V i)) :
    IsOpen {f : K X | f.val ∈ basic X U F V} := by
  letI : TopologicalSpace (ℕ → X) := powerTopology X
  exact isOpen_induced (isOpen_generateFrom_of_mem ⟨U, F, V, hU, hV, rfl⟩)
theorem open_tube (U : Set X) (hU : IsOpen U) :
    IsOpen {f : K X | Set.range f.val ⊆ U} := by
  simpa [basic] using open_basic X U ∅ (fun _ => Set.univ) hU (by simp)
theorem open_coordinate (i : ℕ) (U : Set X) (hU : IsOpen U) :
    IsOpen {f : K X | f.val i ∈ U} := by
  simpa [basic] using open_basic X Set.univ {i} (fun _ => U) isOpen_univ
    (by intros; exact hU)
theorem continuous_coordinate (i : ℕ) : Continuous (fun f : K X => f.val i) :=
  continuous_def.mpr fun U hU => open_coordinate X i U hU

def MainClaim : Prop := SecondCountableTopology (K X) ∧
  IsLindelof (Set.univ : Set (K X)) ∧ ¬ IsSigmaCompact (Set.univ : Set (K X))
end VietorisOrdinals
