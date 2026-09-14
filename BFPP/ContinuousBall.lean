import BFPP.Transfer
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The closed unit ball of real continuous functions -/

namespace BFPP

set_option autoImplicit false

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

theorem continuousBall_abs_le (f : UnitBall C(K, ℝ)) (t : K) : |f.val t| ≤ 1 := by
  have h : |f.val t| ≤ ‖f.val‖ := by
    simpa only [Real.norm_eq_abs] using f.val.norm_coe_le_norm t
  exact h.trans f.property

theorem continuousBall_bounds (f : UnitBall C(K, ℝ)) (t : K) :
    -1 ≤ f.val t ∧ f.val t ≤ 1 := abs_le.mp (continuousBall_abs_le f t)

theorem continuousMap_abs_sub_le_dist (f g : C(K, ℝ)) (t : K) :
    |f t - g t| ≤ dist f g := by
  simpa only [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t

/-- The classical affine sign-extension map, on the whole closed unit ball. -/
noncomputable def signStep (h : C(K, ℝ)) (hh : ∀ t, |h t| ≤ 1)
    (f : UnitBall C(K, ℝ)) : UnitBall C(K, ℝ) := by
  let g : C(K, ℝ) := ⟨fun t => (1 - |h t|) * f.val t + h t, by fun_prop⟩
  refine ⟨g, (ContinuousMap.norm_le g (by norm_num)).2 ?_⟩
  intro t
  change |(1 - |h t|) * f.val t + h t| ≤ 1
  have hp : 0 ≤ 1 - |h t| := sub_nonneg.mpr (hh t)
  calc
    |(1 - |h t|) * f.val t + h t| ≤ |(1 - |h t|) * f.val t| + |h t| :=
      abs_add_le _ _
    _ = (1 - |h t|) * |f.val t| + |h t| := by rw [abs_mul, abs_of_nonneg hp]
    _ ≤ (1 - |h t|) * 1 + |h t| :=
      add_le_add (mul_le_mul_of_nonneg_left (continuousBall_abs_le f t) hp) le_rfl
    _ = 1 := by ring

@[simp] theorem signStep_apply (h : C(K, ℝ)) (hh : ∀ t, |h t| ≤ 1)
    (f : UnitBall C(K, ℝ)) (t : K) :
    (signStep h hh f).val t = (1 - |h t|) * f.val t + h t := rfl

theorem signStep_nonexpansive (h : C(K, ℝ)) (hh : ∀ t, |h t| ≤ 1) :
    LipschitzWith 1 (signStep h hh) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  change dist (signStep h hh f).val (signStep h hh g).val ≤ dist f g
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro t
  rw [Real.dist_eq, signStep_apply, signStep_apply]
  have hp : 0 ≤ 1 - |h t| := sub_nonneg.mpr (hh t)
  have hp' : 1 - |h t| ≤ 1 := by linarith [abs_nonneg (h t)]
  calc
    |(1 - |h t|) * f.val t + h t - ((1 - |h t|) * g.val t + h t)| =
        |(1 - |h t|) * (f.val t - g.val t)| := by congr 1 <;> ring
    _ = (1 - |h t|) * |f.val t - g.val t| := by rw [abs_mul, abs_of_nonneg hp]
    _ ≤ 1 * |f.val t - g.val t| := mul_le_mul_of_nonneg_right hp' (abs_nonneg _)
    _ ≤ dist f g := by
      rw [one_mul]
      exact continuousMap_abs_sub_le_dist f.val g.val t

theorem signStep_fixedPoint_positive (h : C(K, ℝ)) (hh : ∀ t, |h t| ≤ 1)
    (f : UnitBall C(K, ℝ)) (hf : signStep h hh f = f) (t : K) (ht : 0 < h t) :
    f.val t = 1 := by
  have he := congrArg (fun z : UnitBall C(K, ℝ) => z.val t) hf
  rw [signStep_apply, abs_of_pos ht] at he
  nlinarith

theorem signStep_fixedPoint_negative (h : C(K, ℝ)) (hh : ∀ t, |h t| ≤ 1)
    (f : UnitBall C(K, ℝ)) (hf : signStep h hh f = f) (t : K) (ht : h t < 0) :
    f.val t = -1 := by
  have he := congrArg (fun z : UnitBall C(K, ℝ) => z.val t) hf
  rw [signStep_apply, abs_of_neg ht] at he
  nlinarith

end BFPP
