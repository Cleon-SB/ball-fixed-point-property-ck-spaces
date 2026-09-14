import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Linarith

/-! # Uniform estimates for real suprema and infima -/

namespace BFPP

set_option autoImplicit false

open Set

universe u
variable {ι : Type u} [Nonempty ι]

theorem abs_ciSup_sub_ciSup_le (f g : ι → ℝ)
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) (d : ℝ)
    (h : ∀ i, |f i - g i| ≤ d) : |(⨆ i, f i) - ⨆ i, g i| ≤ d := by
  have hfg : (⨆ i, f i) ≤ (⨆ i, g i) + d := by
    apply ciSup_le
    intro i
    have hi := (abs_le.mp (h i)).2
    have hgi := le_ciSup hg i
    linarith
  have hgf : (⨆ i, g i) ≤ (⨆ i, f i) + d := by
    apply ciSup_le
    intro i
    have hi := (abs_le.mp (h i)).1
    have hfi := le_ciSup hf i
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_ciInf_sub_ciInf_le (f g : ι → ℝ)
    (hf : BddBelow (range f)) (hg : BddBelow (range g)) (d : ℝ)
    (h : ∀ i, |f i - g i| ≤ d) : |(⨅ i, f i) - ⨅ i, g i| ≤ d := by
  have hfg : (⨅ i, f i) - d ≤ ⨅ i, g i := by
    apply le_ciInf
    intro i
    have hi := (abs_le.mp (h i)).2
    have hfi := ciInf_le hf i
    linarith
  have hgf : (⨅ i, g i) - d ≤ ⨅ i, f i := by
    apply le_ciInf
    intro i
    have hi := (abs_le.mp (h i)).1
    have hgi := ciInf_le hg i
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem ciSup_const_of_nonempty (r : ℝ) : (⨆ _ : ι, r) = r := by
  exact ciSup_const

end BFPP
