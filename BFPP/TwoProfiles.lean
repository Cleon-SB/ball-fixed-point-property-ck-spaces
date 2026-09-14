import BFPP.Profiles
import BFPP.Center

/-! # The invariant two-tail domain and its common center -/

namespace BFPP

set_option autoImplicit false

universe u v
variable {ι : Type u} {κ : Type v}
  [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

abbrev TwoProfile (ι : Type u) (κ : Type v)
    [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ] :=
  {z : Profile ι × Profile κ // 2 ≤ z.1.tail + z.2.tail}

namespace TwoProfile

noncomputable def center (z : TwoProfile ι κ) : ℝ :=
  commonCenter z.val.1.tail z.val.2.tail

theorem center_bounds (z : TwoProfile ι κ) :
    -1 ≤ z.center ∧ z.center ≤ 1 ∧
    1 - z.val.1.tail ≤ z.center ∧ z.center ≤ z.val.2.tail - 1 :=
  commonCenter_bounds ⟨z.val.1.tail_nonneg, z.val.1.tail_le_two⟩
    ⟨z.val.2.tail_nonneg, z.val.2.tail_le_two⟩ z.property

theorem center_nonexpansive : LipschitzWith 1 (center : TwoProfile ι κ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  change |commonCenter z.val.1.tail z.val.2.tail -
    commonCenter w.val.1.tail w.val.2.tail| ≤ dist z w
  apply commonCenter_nonexpansive_bound
  · have h := Profile.tail_nonexpansive.dist_le_mul z.val.1 w.val.1
    have hp : dist z.val.1 w.val.1 ≤ dist z w := le_max_left _ _
    apply le_trans _ hp
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using h
  · have h := Profile.tail_nonexpansive.dist_le_mul z.val.2 w.val.2
    have hp : dist z.val.2 w.val.2 ≤ dist z w := le_max_right _ _
    apply le_trans _ hp
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using h

section Delay

variable [NoMaxOrder ι] [NoMaxOrder κ]

noncomputable def delay (z : TwoProfile ι κ) : TwoProfile ι κ :=
  ⟨(z.val.1.delay, z.val.2.delay), by
    simpa only [Profile.tail_delay] using z.property⟩

theorem delay_nonexpansive : LipschitzWith 1 (delay : TwoProfile ι κ → TwoProfile ι κ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  change max (dist z.val.1.delay w.val.1.delay) (dist z.val.2.delay w.val.2.delay) ≤
    max (dist z.val.1 w.val.1) (dist z.val.2 w.val.2)
  apply max_le_max
  · simpa only [NNReal.coe_one, one_mul] using
      Profile.delay_nonexpansive.dist_le_mul z.val.1 w.val.1
  · simpa only [NNReal.coe_one, one_mul] using
      Profile.delay_nonexpansive.dist_le_mul z.val.2 w.val.2

theorem no_subsolution [WellFoundedLT ι] [WellFoundedLT κ] (z : TwoProfile ι κ) :
    ¬ z ≤ z.delay := by
  intro h
  have ha := Profile.subsolution_eq_zero z.val.1 h.1
  have hb := Profile.subsolution_eq_zero z.val.2 h.2
  have hA : z.val.1.tail = 0 := by
    simp only [Profile.tail, BoundedFamily.supremum, ha, ciSup_const]
  have hB : z.val.2.tail = 0 := by
    simp only [Profile.tail, BoundedFamily.supremum, hb, ciSup_const]
  have hc := z.property
  rw [hA, hB] at hc
  norm_num at hc

theorem fixedPointFree_delay [WellFoundedLT ι] [WellFoundedLT κ] (z : TwoProfile ι κ) :
    z.delay ≠ z := by
  intro h
  apply no_subsolution z
  exact h.ge

end Delay
end TwoProfile
end BFPP
