import VietorisOrdinals
open Set
open scoped Ordinal Cardinal
open VietorisOrdinals

-- Check the explicit conclusion, independently of the MainClaim abbreviation.
example (a : Ordinal.{0}) (hlo : ω < a) (hhi : a < ω₁) :
    SecondCountableTopology (K (OrdinalSpace a)) ∧
    IsLindelof (Set.univ : Set (K (OrdinalSpace a))) ∧
    ¬ IsSigmaCompact (Set.univ : Set (K (OrdinalSpace a))) :=
  ordinal_main a hlo hhi
example (a : Ordinal.{0}) : OrderTopology (OrdinalSpace a) := inferInstance
example (a : Ordinal.{0}) (hlo : ω < a) (hhi : a < ω₁) :
    ¬ Menger (K (OrdinalSpace a)) := (ordinal_full a hlo hhi).2

#check VietorisOrdinals.ordinal_main
#check VietorisOrdinals.ordinal_full
#check VietorisOrdinals.second_countable
#check VietorisOrdinals.ordinal_subsets_countable
#print VietorisOrdinals.K
#print VietorisOrdinals.basic
#print VietorisOrdinals.generators
#print VietorisOrdinals.powerTopology
#print VietorisOrdinals.kTopology
#print VietorisOrdinals.ordinalTopology
#print VietorisOrdinals.OrdinalSpace
#print VietorisOrdinals.MainClaim
#print VietorisOrdinals.Menger
#print axioms VietorisOrdinals.second_countable
#print axioms VietorisOrdinals.not_sigmaCompact
#print axioms VietorisOrdinals.not_menger
#print axioms VietorisOrdinals.ordinal_main
#print axioms VietorisOrdinals.ordinal_full
#print axioms VietorisOrdinals.ordinal_subsets_countable
