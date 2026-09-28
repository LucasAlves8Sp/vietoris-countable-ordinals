import VietorisOrdinals.Countability
import VietorisOrdinals.Obstruction
noncomputable section
open Set TopologicalSpace Order
open scoped Cardinal Ordinal
namespace VietorisOrdinals

/-- The ordinary order topology on actual mathlib ordinals. -/
instance ordinalTopology : TopologicalSpace Ordinal.{0} := Preorder.topology _
instance ordinalOrderTopology : OrderTopology Ordinal.{0} := ⟨rfl⟩
abbrev OrdinalSpace (a : Ordinal.{0}) := Set.Iio a

theorem countable_order_second_countable (Y : Type*) [LinearOrder Y]
    [TopologicalSpace Y] [OrderTopology Y] [Countable Y] :
    SecondCountableTopology Y := by
  have he : {s : Set Y | ∃ a, s = Ioi a ∨ s = Iio a} =
      Set.range (Ioi : Y → Set Y) ∪ Set.range (Iio : Y → Set Y) := by
    ext s
    simp only [Set.mem_setOf_eq,Set.mem_union,Set.mem_range]
    constructor
    · rintro ⟨a,h|h⟩
      · exact Or.inl ⟨a,h.symm⟩
      · exact Or.inr ⟨a,h.symm⟩
    · rintro (⟨a,h⟩|⟨a,h⟩)
      · exact ⟨a,Or.inl h.symm⟩
      · exact ⟨a,Or.inr h.symm⟩
  have ht := OrderTopology.topology_eq_generate_intervals (α := Y)
  rw [he] at ht
  exact ⟨⟨_,(Set.countable_range _).union (Set.countable_range _),ht⟩⟩

theorem ordinalSpace_countable (a : Ordinal.{0}) (ha : a < ω₁) :
    Countable (OrdinalSpace a) := by
  have hc : a.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp ha
  have hle : a.card ≤ Cardinal.aleph0 := by
    rw [← Cardinal.succ_aleph0] at hc
    exact Order.lt_succ_iff.mp hc
  haveI : Countable a.toType := Cardinal.mk_le_aleph0_iff.mp (by
    simpa only [Cardinal.mk_toType] using hle)
  exact Countable.of_equiv a.toType (Ordinal.enumIsoToType a).toEquiv.symm

def ordinalSequence (a : Ordinal.{0}) (ha : ω < a) : Option ℕ → OrdinalSpace a
  | none => ⟨ω,ha⟩
  | some n => ⟨n,(Ordinal.nat_lt_omega0 n).trans ha⟩

theorem ordinalSequence_injective (a : Ordinal.{0}) (ha : ω < a) :
    Function.Injective (ordinalSequence a ha) := by
  intro x y h
  have hv := congrArg Subtype.val h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some n => exact ((Ordinal.nat_lt_omega0 n).ne hv.symm).elim
  | some m =>
    cases y with
    | none => exact ((Ordinal.nat_lt_omega0 m).ne hv).elim
    | some n =>
      have : m = n := Nat.cast_injective hv
      exact congrArg some this

theorem ordinalSequence_compact (a : Ordinal.{0}) (ha : ω < a) :
    IsCompact (Set.range (ordinalSequence a ha)) := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val : OrdinalSpace a → Ordinal) '' Set.range (ordinalSequence a ha) =
      Icc 0 ω := by
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      cases z with
      | none => exact ⟨Ordinal.zero_le _,le_rfl⟩
      | some n => exact ⟨Ordinal.zero_le _,(Ordinal.nat_lt_omega0 n).le⟩
    · intro hx
      rcases lt_or_eq_of_le hx.2 with hx | hx
      · obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hx
        exact ⟨ordinalSequence a ha (some n),Set.mem_range_self _,rfl⟩
      · subst x
        exact ⟨ordinalSequence a ha none,Set.mem_range_self _,rfl⟩
  rw [he]
  exact isCompact_Icc

theorem ordinal_nat_open (n : ℕ) : IsOpen ({(n : Ordinal.{0})} : Set Ordinal) := by
  cases n with
  | zero =>
    have he : ({(0 : Ordinal)} : Set Ordinal) = Iio (succ 0) := by
      ext x
      simp only [Set.mem_singleton_iff,Set.mem_Iio,Order.lt_succ_iff]
      exact ⟨fun h => h ▸ le_rfl,fun h => le_antisymm h (Ordinal.zero_le _)⟩
    change IsOpen ({(0 : Ordinal)} : Set Ordinal)
    rw [he]
    exact isOpen_Iio
  | succ n =>
    have he : ({succ (n : Ordinal)} : Set Ordinal) = Ioo (n : Ordinal) (succ (succ n)) := by
      ext x
      simp only [Set.mem_singleton_iff,Set.mem_Ioo,Order.lt_succ_iff]
      constructor
      · intro h
        subst x
        exact ⟨Order.lt_succ _,le_rfl⟩
      · intro h
        exact le_antisymm h.2 (Order.succ_le_iff.mpr h.1)
    have hn : ((n+1 : ℕ) : Ordinal) = succ (n : Ordinal) := by
      rw [Nat.cast_add,Nat.cast_one,Ordinal.add_one_eq_succ]
    rw [hn,he]
    exact isOpen_Ioo

theorem ordinalSequence_open (a : Ordinal.{0}) (ha : ω < a) (n : ℕ) :
    IsOpen ({ordinalSequence a ha (some n)} : Set (OrdinalSpace a)) := by
  have he : ({ordinalSequence a ha (some n)} : Set (OrdinalSpace a)) =
      (Subtype.val : OrdinalSpace a → Ordinal) ⁻¹' {(n : Ordinal)} := by
    ext x
    simp only [Set.mem_singleton_iff,Set.mem_preimage,Subtype.ext_iff]
    rfl
  rw [he]
  exact (ordinal_nat_open n).preimage continuous_subtype_val

/-- Full Question 1 theorem on the ordinal interval {b : Ordinal | b < a},
with its inherited order topology and the actual compact-range construction. -/
theorem ordinal_main (a : Ordinal.{0}) (hlo : ω < a) (hhi : a < ω₁) :
    MainClaim (OrdinalSpace a) := by
  letI := ordinalSpace_countable a hhi
  letI := countable_order_second_countable (OrdinalSpace a)
  exact ⟨second_countable _,lindelof _,not_sigmaCompact _ (ordinalSequence a hlo)
    (ordinalSequence_injective a hlo) (ordinalSequence_compact a hlo)
    (ordinalSequence_open a hlo)⟩
end VietorisOrdinals
