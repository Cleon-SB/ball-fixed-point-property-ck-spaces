import BFPP.StepFunctions
import BFPP.StepAlgebra
import BFPP.ContinuousBall
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Extension of positive synthesis from finite step functions

The estimates first expose density as a hypothesis. The existence theorem at
the end discharges it using `stepCombination_denseRange`.
-/

namespace BFPP

set_option autoImplicit false

open Set Order
open scoped ZeroAtInfty

universe u v
variable {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K]

noncomputable def weightedCombination (w : ι → C(K, ℝ)) : (ι →₀ ℝ) →ₗ[ℝ] C(K, ℝ) :=
  Finsupp.linearCombination ℝ w

theorem weightedCombination_apply (w : ι → C(K, ℝ)) (c : ι →₀ ℝ) (t : K) :
    weightedCombination w c t = ∑ i ∈ c.support, c i * w i t := by
  simp [weightedCombination, Finsupp.linearCombination_apply, Finsupp.sum]

theorem weightedCombination_norm_le (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (c : ι →₀ ℝ) : ‖weightedCombination w c‖ ≤ ‖stepCombination c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  rw [Real.norm_eq_abs, weightedCombination_apply]
  apply finite_synthesis_abs_bound_finset c.support c (fun i => w i t)
    ‖stepCombination c‖ (norm_nonneg _) (hw t) (fun i _hi => hb i t)
  intro i
  rw [← stepCombination_apply]
  exact c0_abs_apply_le_norm _ i

noncomputable def synthesisOperator (w : ι → C(K, ℝ)) : C₀(ι, ℝ) →L[ℝ] C(K, ℝ) :=
  (weightedCombination w).extendOfNorm stepCombination

theorem synthesisOperator_stepCombination (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ))) (c : ι →₀ ℝ) :
    synthesisOperator w (stepCombination c) = weightedCombination w c := by
  apply LinearMap.extendOfNorm_eq hdense
  exact ⟨1, fun c => by simpa only [one_mul] using weightedCombination_norm_le w hw hb c⟩

theorem synthesisOperator_initialStep (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ))) (i : ι) :
    synthesisOperator w (initialStep i) = w i := by
  rw [← stepCombination_single i, synthesisOperator_stepCombination w hw hb hdense]
  simp [weightedCombination, Finsupp.linearCombination_single]

theorem synthesisOperator_norm_le (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ))) :
    ‖synthesisOperator w‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le hdense (by norm_num)
  intro c
  simpa only [one_mul] using weightedCombination_norm_le w hw hb c

theorem synthesisOperator_nonexpansive (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ))) :
    LipschitzWith 1 (synthesisOperator w) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
  calc
    ‖synthesisOperator w (f - g)‖ ≤ ‖synthesisOperator w‖ * ‖f - g‖ :=
      (synthesisOperator w).le_opNorm _
    _ ≤ 1 * ‖f - g‖ := mul_le_mul_of_nonneg_right
      (synthesisOperator_norm_le w hw hb hdense) (norm_nonneg _)
    _ = ‖f - g‖ := one_mul _

theorem weightedCombination_bounds (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (c : ι →₀ ℝ) (m M : ℝ) (hm : m ≤ 0) (hM : 0 ≤ M)
    (hf : ∀ i, m ≤ stepCombination c i ∧ stepCombination c i ≤ M) (t : K) :
    m ≤ weightedCombination w c t ∧ weightedCombination w c t ≤ M := by
  rw [weightedCombination_apply]
  apply finite_synthesis_bounds_finset c.support c (fun i => w i t) m M hm hM
    (hw t) (fun i _hi => hb i t)
  intro i
  simpa only [stepCombination_apply] using hf i

/-- Uniform approximation extends the finite order estimates, including positivity. -/
theorem synthesisOperator_preserves_bounds (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ)))
    (f : C₀(ι, ℝ)) (m M : ℝ) (hm : m ≤ 0) (hM : 0 ≤ M)
    (hf : ∀ i, m ≤ f i ∧ f i ≤ M) (t : K) :
    m ≤ synthesisOperator w f t ∧ synthesisOperator w f t ≤ M := by
  have happrox : ∀ ε : ℝ, 0 < ε → m - ε ≤ synthesisOperator w f t ∧
      synthesisOperator w f t ≤ M + ε := by
    intro ε hε
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp hdense f (ε / 3) (by linarith)
    have hstep : ∀ i, m - ε / 3 ≤ stepCombination c i ∧ stepCombination c i ≤ M + ε / 3 := by
      intro i
      have hi := c0_abs_sub_le_dist f (stepCombination c) i
      have hib := abs_le.mp (hi.trans hc.le)
      have hfi := hf i
      exact ⟨by linarith, by linarith⟩
    have hfinite := weightedCombination_bounds w hw hb c (m - ε / 3) (M + ε / 3)
      (by linarith) (by linarith) hstep t
    have hlip := (synthesisOperator_nonexpansive w hw hb hdense).dist_le_mul f (stepCombination c)
    simp only [NNReal.coe_one, one_mul] at hlip
    have hp := continuousMap_abs_sub_le_dist (synthesisOperator w f)
      (synthesisOperator w (stepCombination c)) t
    have hdiff := abs_le.mp (hp.trans (hlip.trans hc.le))
    rw [synthesisOperator_stepCombination w hw hb hdense] at hdiff
    exact ⟨by linarith, by linarith⟩
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    have h := (happrox ε hε).1
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).2

theorem synthesisOperator_positive (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ)))
    (f : C₀(ι, ℝ)) (hf : ∀ i, 0 ≤ f i) (t : K) : 0 ≤ synthesisOperator w f t := by
  have hbounds : ∀ i, 0 ≤ f i ∧ f i ≤ ‖f‖ := fun i =>
    ⟨hf i, (le_abs_self _).trans (c0_abs_apply_le_norm f i)⟩
  exact (synthesisOperator_preserves_bounds w hw hb hdense f 0 ‖f‖ le_rfl
    (norm_nonneg _) hbounds t).1

theorem synthesisOperator_zero_at (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (hdense : DenseRange (stepCombination : (ι →₀ ℝ) → C₀(ι, ℝ)))
    (t : K) (ht : ∀ i, w i t = 0) (f : C₀(ι, ℝ)) : synthesisOperator w f t = 0 := by
  refine hdense.induction_on f ?_ ?_
  · exact isClosed_eq ((ContinuousMap.evalCLM ℝ t).continuous.comp (synthesisOperator w).continuous)
      continuous_const
  · intro c
    rw [synthesisOperator_stepCombination w hw hb hdense, weightedCombination_apply]
    simp [ht]

theorem synthesisOperator_lower_on_initialSegment (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (f : C₀(ι, ℝ)) (hf : ∀ i, 0 ≤ f i) (a : ι) (t : K) (hwt : w a t = 1)
    (L : ℝ) (hL : ∀ i, i ≤ a → L ≤ f i) : L ≤ synthesisOperator w f t := by
  have hp : ∀ i, 0 ≤ (f - L • initialStep a) i := by
    intro i
    simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
      initialStep_apply, smul_eq_mul]
    by_cases hi : i ≤ a
    · simp only [if_pos hi, mul_one]
      exact sub_nonneg.mpr (hL i hi)
    · simpa only [if_neg hi, mul_zero, sub_zero] using hf i
  have h := synthesisOperator_positive w hw hb stepCombination_denseRange
    (f - L • initialStep a) hp t
  rw [map_sub, map_smul, synthesisOperator_initialStep w hw hb stepCombination_denseRange] at h
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul, hwt, mul_one] at h
  linarith

theorem positiveSynthesis_exists (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1) :
    ∃ S : C₀(ι, ℝ) →L[ℝ] C(K, ℝ), ‖S‖ ≤ 1 ∧
      (∀ f, (∀ i, 0 ≤ f i) → ∀ t, 0 ≤ S f t) ∧ (∀ i, S (initialStep i) = w i) :=
  ⟨synthesisOperator w,
    synthesisOperator_norm_le w hw hb stepCombination_denseRange,
    synthesisOperator_positive w hw hb stepCombination_denseRange,
    synthesisOperator_initialStep w hw hb stepCombination_denseRange⟩

theorem positiveSynthesis_unique (S T : C₀(ι, ℝ) →L[ℝ] C(K, ℝ))
    (h : ∀ i, S (initialStep i) = T (initialStep i)) : S = T := by
  apply ContinuousLinearMap.ext
  intro f
  refine stepCombination_denseRange.induction_on f ?_ ?_
  · exact isClosed_eq S.continuous T.continuous
  · intro c
    rw [stepCombination_eq_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_smul, map_smul, h i]

end BFPP
