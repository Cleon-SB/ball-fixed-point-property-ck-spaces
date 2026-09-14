import BFPP.Realization
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Order.SuccPred.Basic

/-! # Concrete ordinal index spaces -/

namespace BFPP

set_option autoImplicit false

open Set Order

universe u

abbrev OrdinalIndex (τ : Ordinal.{u}) := Set.Iio τ

variable (τ : Ordinal.{u}) [hτ : Fact (IsSuccLimit τ)]

instance ordinalIndexOrderBot : OrderBot (OrdinalIndex τ) where
  bot := ⟨0, hτ.out.pos⟩
  bot_le i := by
    change (0 : Ordinal.{u}) ≤ i.val
    exact bot_le

instance ordinalIndexNoMaxOrder : NoMaxOrder (OrdinalIndex τ) :=
  hτ.out.isSuccPrelimit.noMaxOrder_Iio

noncomputable instance ordinalIndexSuccOrder : SuccOrder (OrdinalIndex τ) :=
  SuccOrder.ofLinearWellFoundedLT _

instance ordinalIndexCompactIcc : CompactIccSpace (OrdinalIndex τ) where
  isCompact_Icc {a b} := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' (Icc a b) = Icc a.val b.val := by
      ext i
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact hj
      · intro hi
        exact ⟨⟨i, lt_of_le_of_lt hi.2 b.property⟩, hi, rfl⟩
    rw [he]
    exact isCompact_Icc

example : OrderTopology (OrdinalIndex τ) := inferInstance
example : CompactIccSpace (OrdinalIndex τ) := inferInstance
example : WellFoundedLT (OrdinalIndex τ) := inferInstance

end BFPP
