import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Logic.Small.Basic

/-! # The size obstruction used to terminate sign propagation -/

namespace BFPP

set_option autoImplicit false

universe u

/-- The ordinals in a universe cannot inject into a type in that same universe. -/
theorem no_injection_from_ordinals (X : Type u) (f : Ordinal.{u} → X) :
    ¬ Function.Injective f := by
  intro hf
  letI : Small.{u} Ordinal.{u} := small_of_injective hf
  have hb : BddAbove (Set.univ : Set Ordinal.{u}) := Ordinal.bddAbove_of_small
  exact not_bddAbove_univ hb

end BFPP
