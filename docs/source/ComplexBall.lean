import BFPP.Necessity
import Mathlib.Analysis.Complex.Basic

/-! # The real construction also yields a map on the complex unit ball -/

namespace BFPP

set_option autoImplicit false

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

noncomputable def ballRealPart (f : UnitBall C(K, ℂ)) : UnitBall C(K, ℝ) :=
  ⟨⟨fun t => (f.val t).re, Complex.continuous_re.comp f.val.continuous⟩, by
    apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro t
    change |(f.val t).re| ≤ 1
    exact (Complex.abs_re_le_norm _).trans ((f.val.norm_coe_le_norm t).trans f.property)⟩

noncomputable def ballComplexify (f : UnitBall C(K, ℝ)) : UnitBall C(K, ℂ) :=
  ⟨⟨fun t => (f.val t : ℂ), Complex.continuous_ofReal.comp f.val.continuous⟩, by
    apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro t
    change ‖(f.val t : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact (f.val.norm_coe_le_norm t).trans f.property⟩

@[simp] theorem ballRealPart_complexify (f : UnitBall C(K, ℝ)) :
    ballRealPart (ballComplexify f) = f := by
  apply Subtype.ext
  ext t
  rfl

theorem ballRealPart_nonexpansive : LipschitzWith 1 (@ballRealPart K _ _) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  change dist (ballRealPart f).val (ballRealPart g).val ≤ dist f.val g.val
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ dist_nonneg).mpr
  intro t
  change ‖(f.val t).re - (g.val t).re‖ ≤ dist f.val g.val
  rw [dist_eq_norm]
  rw [← Complex.sub_re, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans ((f.val - g.val).norm_coe_le_norm t)

theorem ballComplexify_nonexpansive : LipschitzWith 1 (@ballComplexify K _ _) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  change dist (ballComplexify f).val (ballComplexify g).val ≤ dist f.val g.val
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ dist_nonneg).mpr
  intro t
  change ‖(f.val t : ℂ) - (g.val t : ℂ)‖ ≤ dist f.val g.val
  rw [dist_eq_norm]
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact (f.val - g.val).norm_coe_le_norm t

theorem complex_fixedPointFree_of_real
    (T : UnitBall C(K, ℝ) → UnitBall C(K, ℝ)) (hT : LipschitzWith 1 T)
    (hfree : ∀ f, T f ≠ f) :
    ∃ S : UnitBall C(K, ℂ) → UnitBall C(K, ℂ), LipschitzWith 1 S ∧ ∀ f, S f ≠ f := by
  refine ⟨fun f => ballComplexify (T (ballRealPart f)),
    nonexpansive_transfer ballRealPart ballComplexify T ballRealPart_nonexpansive
      ballComplexify_nonexpansive hT, ?_⟩
  intro f hf
  have h := congrArg ballRealPart hf
  exact hfree (ballRealPart f) (by simpa only [ballRealPart_complexify] using h)

theorem exists_complex_fixedPointFree_of_not_ED [T2Space K] (hK : ¬ ExtremallyDisconnected K) :
    ∃ S : UnitBall C(K, ℂ) → UnitBall C(K, ℂ), LipschitzWith 1 S ∧ ∀ f, S f ≠ f := by
  obtain ⟨T, hT, hfree⟩ := exists_nonexpansive_fixedPointFree_of_not_ED hK
  exact complex_fixedPointFree_of_real T hT hfree

end BFPP
