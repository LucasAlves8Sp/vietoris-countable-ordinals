import VietorisOrdinals.Ordinals
import VietorisOrdinals.Menger
noncomputable section
open Set
open scoped Ordinal Cardinal
namespace VietorisOrdinals

theorem ordinal_not_menger (a : Ordinal.{0}) (hlo : ω < a) :
    ¬ Menger (K (OrdinalSpace a)) :=
  not_menger _ (ordinalSequence a hlo) (ordinalSequence_injective a hlo)
    (ordinalSequence_compact a hlo) (ordinalSequence_open a hlo)

/-- All assertions of the principal theorem, for actual countable ordinals. -/
theorem ordinal_full (a : Ordinal.{0}) (hlo : ω < a) (hhi : a < ω₁) :
    MainClaim (OrdinalSpace a) ∧ ¬ Menger (K (OrdinalSpace a)) :=
  ⟨ordinal_main a hlo hhi,ordinal_not_menger a hlo⟩

/-- All subsets of a countable ordinal, in particular all compact subsets,
have cardinality at most aleph zero. -/
theorem ordinal_subsets_countable (a : Ordinal.{0}) (hhi : a < ω₁)
    (C : Set (OrdinalSpace a)) : Cardinal.mk C ≤ Cardinal.aleph0 := by
  letI := ordinalSpace_countable a hhi
  exact Cardinal.mk_le_aleph0
end VietorisOrdinals
