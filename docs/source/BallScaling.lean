import BFPP.Transfer
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! # BFPP on the unit ball and on arbitrary nonempty closed balls -/

namespace BFPP

set_option autoImplicit false

/-- A positive similarity transports the nonexpansive fixed point property. -/
theorem fixedPoint_property_of_similarity {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ Y) (r : ℝ) (hr : 0 < r)
    (he : ∀ x y, dist (e x) (e y) = r * dist x y)
    (hX : ∀ T : X → X, LipschitzWith 1 T → ∃ x, T x = x) :
    ∀ T : Y → Y, LipschitzWith 1 T → ∃ y, T y = y := by
  intro T hT
  let S : X → X := fun x => e.symm (T (e x))
  have hS : LipschitzWith 1 S := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (mul_le_mul_iff_right₀ hr).mp
    calc
      r * dist (S x) (S y) = dist (e (S x)) (e (S y)) := (he _ _).symm
      _ = dist (T (e x)) (T (e y)) := by simp only [S, Equiv.apply_symm_apply]
      _ ≤ dist (e x) (e y) := by simpa only [NNReal.coe_one, one_mul] using hT.dist_le_mul (e x) (e y)
      _ = r * dist x y := he x y
  obtain ⟨x, hx⟩ := hX S hS
  refine ⟨e x, ?_⟩
  have hh := congrArg e hx
  simpa only [S, Equiv.apply_symm_apply] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def ballScaleEquiv (c : E) (r : ℝ) (hr : 0 < r) :
    UnitBall E ≃ Metric.closedBall c r where
  toFun x := ⟨c + r • x.val, by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have he : c + r • x.val - c = r • x.val := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left x.property hr.le).trans_eq (mul_one r)⟩
  invFun y := ⟨r⁻¹ • (y.val - c), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hy : ‖y.val - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using y.property
    exact (mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hr.le)).trans_eq (inv_mul_cancel₀ hr.ne')⟩
  left_inv x := by
    apply Subtype.ext
    change r⁻¹ • (c + r • x.val - c) = x.val
    have he : c + r • x.val - c = r • x.val := by abel
    rw [he, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  right_inv y := by
    apply Subtype.ext
    change c + r • (r⁻¹ • (y.val - c)) = y.val
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel

theorem ballScaleEquiv_dist (c : E) (r : ℝ) (hr : 0 < r) (x y : UnitBall E) :
    dist (ballScaleEquiv c r hr x) (ballScaleEquiv c r hr y) = r * dist x y := by
  change dist (c + r • x.val) (c + r • y.val) = r * dist x.val y.val
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]

theorem closedBall_fixedPoint_of_hasBFPP (hE : HasBFPP E) (c : E) (r : ℝ) (hr : 0 ≤ r)
    (T : Metric.closedBall c r → Metric.closedBall c r) (hT : LipschitzWith 1 T) :
    ∃ x, T x = x := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r
    let x : Metric.closedBall c 0 := ⟨c, by simp⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact dist_le_zero.mp (T x).property
  · exact fixedPoint_property_of_similarity (ballScaleEquiv c r hpos) r hpos
      (ballScaleEquiv_dist c r hpos) hE T hT

/-- Radius zero is included; negative-radius balls are empty and intentionally excluded. -/
theorem hasBFPP_iff_all_closedBalls : HasBFPP E ↔
    ∀ c : E, ∀ r : ℝ, 0 ≤ r →
      ∀ T : Metric.closedBall c r → Metric.closedBall c r,
        LipschitzWith 1 T → ∃ x, T x = x := by
  refine ⟨fun h c r hr T hT => closedBall_fixedPoint_of_hasBFPP h c r hr T hT, ?_⟩
  intro h
  let e := ballScaleEquiv (0 : E) 1 (by norm_num : (0 : ℝ) < 1)
  have he : ∀ x y, dist (e.symm x) (e.symm y) = 1 * dist x y := by
    intro x y
    have hh := ballScaleEquiv_dist (0 : E) 1 (by norm_num : (0 : ℝ) < 1) (e.symm x) (e.symm y)
    change dist (e (e.symm x)) (e (e.symm y)) = 1 * dist (e.symm x) (e.symm y) at hh
    simpa only [Equiv.apply_symm_apply, one_mul] using hh.symm
  exact fixedPoint_property_of_similarity e.symm 1 (by norm_num) he (h 0 1 (by norm_num))

theorem closedBall_negative_empty (c : E) (r : ℝ) (hr : r < 0) :
    Metric.closedBall c r = ∅ := Metric.closedBall_eq_empty.mpr hr

end BFPP
