import BFPP.Families
import BFPP.TwoProfileGeometry

/-! # Realization on the whole closed unit ball from an inseparable pair -/

namespace BFPP

set_option autoImplicit false

open Set
open scoped ZeroAtInfty

universe u v w
variable {K : Type u} {ι : Type v} {κ : Type w}
  [TopologicalSpace K] [CompactSpace K]
  [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]
  [LinearOrder κ] [OrderBot κ] [SuccOrder κ] [NoMaxOrder κ]
  [TopologicalSpace κ] [OrderTopology κ] [CompactIccSpace κ]

namespace InseparablePair

noncomputable def positiveInput (z : TwoProfile ι κ) : C₀(ι, ℝ) :=
  z.val.1.positiveTail z.center z.center_bounds.2.2.1

noncomputable def negativeInput (z : TwoProfile ι κ) : C₀(κ, ℝ) :=
  z.val.2.positiveTail (-z.center) (by have h := z.center_bounds.2.2.2; linarith)

noncomputable def positiveOutput (F : InseparablePair K ι κ) (z : TwoProfile ι κ) : C(K, ℝ) :=
  synthesisOperator F.positive.functions (positiveInput z)

noncomputable def negativeOutput (F : InseparablePair K ι κ) (z : TwoProfile ι κ) : C(K, ℝ) :=
  synthesisOperator F.negative.functions (negativeInput z)

theorem positiveOutput_zero (F : InseparablePair K ι κ) (t : K)
    (ht : ∀ i, F.positive.functions i t = 0) (z : TwoProfile ι κ) : F.positiveOutput z t = 0 :=
  synthesisOperator_zero_at _ F.positive.monotone F.positive.bounds
    stepCombination_denseRange t ht _

theorem negativeOutput_zero (F : InseparablePair K ι κ) (t : K)
    (ht : ∀ j, F.negative.functions j t = 0) (z : TwoProfile ι κ) : F.negativeOutput z t = 0 :=
  synthesisOperator_zero_at _ F.negative.monotone F.negative.bounds
    stepCombination_denseRange t ht _

theorem positiveOutput_centered_bounds (F : InseparablePair K ι κ) (z : TwoProfile ι κ) (t : K) :
    -1 ≤ z.center + F.positiveOutput z t ∧ z.center + F.positiveOutput z t ≤ 1 :=
  centeredSynthesis_bounds _ F.positive.monotone F.positive.bounds z.val.1 z.center _
    ⟨z.center_bounds.1, z.center_bounds.2.1⟩ t

theorem negativeOutput_centered_bounds (F : InseparablePair K ι κ) (z : TwoProfile ι κ) (t : K) :
    -1 ≤ -z.center + F.negativeOutput z t ∧ -z.center + F.negativeOutput z t ≤ 1 := by
  apply centeredSynthesis_bounds _ F.negative.monotone F.negative.bounds z.val.2 (-z.center) _ _ t
  have h := z.center_bounds
  exact ⟨by linarith [h.2.1], by linarith [h.1]⟩

noncomputable def synthesizeMap (F : InseparablePair K ι κ) (z : TwoProfile ι κ) : C(K, ℝ) :=
  ContinuousMap.const K z.center + F.positiveOutput z - F.negativeOutput z

@[simp] theorem synthesizeMap_apply (F : InseparablePair K ι κ) (z : TwoProfile ι κ) (t : K) :
    F.synthesizeMap z t = z.center + F.positiveOutput z t - F.negativeOutput z t := rfl

theorem synthesizeMap_bounds (F : InseparablePair K ι κ) (z : TwoProfile ι κ) (t : K) :
    -1 ≤ F.synthesizeMap z t ∧ F.synthesizeMap z t ≤ 1 := by
  rw [synthesizeMap_apply]
  rcases F.disjoint_channels t with hp | hn
  · rw [F.positiveOutput_zero t hp z]
    have h := F.negativeOutput_centered_bounds z t
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · rw [F.negativeOutput_zero t hn z, sub_zero]
    exact F.positiveOutput_centered_bounds z t

noncomputable def synthesize (F : InseparablePair K ι κ) (z : TwoProfile ι κ) :
    UnitBall C(K, ℝ) :=
  ⟨F.synthesizeMap z, (ContinuousMap.norm_le _ (by norm_num)).mpr
    (fun t => abs_le.mpr (F.synthesizeMap_bounds z t))⟩

theorem positiveOutput_centered_dist (F : InseparablePair K ι κ) (z z' : TwoProfile ι κ) (t : K) :
    |(z.center + F.positiveOutput z t) - (z'.center + F.positiveOutput z' t)| ≤ dist z z' := by
  have hcenter : |z.center - z'.center| ≤ dist z z' := by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
      TwoProfile.center_nonexpansive.dist_le_mul z z'
  exact centeredSynthesis_dist _ F.positive.monotone F.positive.bounds z.val.1 z'.val.1
    z.center z'.center _ _ (dist z z') (le_max_left _ _) hcenter t

theorem negativeOutput_centered_dist (F : InseparablePair K ι κ) (z z' : TwoProfile ι κ) (t : K) :
    |(-z.center + F.negativeOutput z t) - (-z'.center + F.negativeOutput z' t)| ≤ dist z z' := by
  have hcenter : |z.center - z'.center| ≤ dist z z' := by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
      TwoProfile.center_nonexpansive.dist_le_mul z z'
  have hneg : |-z.center - (-z'.center)| ≤ dist z z' := by
    simpa only [neg_sub_neg, abs_sub_comm] using hcenter
  exact centeredSynthesis_dist _ F.negative.monotone F.negative.bounds z.val.2 z'.val.2
    (-z.center) (-z'.center) _ _ (dist z z') (le_max_right _ _) hneg t

theorem synthesize_nonexpansive (F : InseparablePair K ι κ) : LipschitzWith 1 F.synthesize := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  simp only [NNReal.coe_one, one_mul]
  change dist (F.synthesizeMap z) (F.synthesizeMap z') ≤ dist z z'
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  rw [Real.dist_eq, synthesizeMap_apply, synthesizeMap_apply]
  rcases F.disjoint_channels t with hp | hn
  · rw [F.positiveOutput_zero t hp z, F.positiveOutput_zero t hp z']
    have h := abs_le.mp (F.negativeOutput_centered_dist z z' t)
    exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
  · rw [F.negativeOutput_zero t hn z, F.negativeOutput_zero t hn z', sub_zero, sub_zero]
    exact F.positiveOutput_centered_dist z z' t

theorem synthesize_at_positive_level (F : InseparablePair K ι κ) (z : TwoProfile ι κ)
    (i : ι) (t : K) (ht : t ∈ F.positive.levels i) :
    1 - z.val.1.val i ≤ (F.synthesize z).val t := by
  change 1 - z.val.1.val i ≤ F.synthesizeMap z t
  rw [synthesizeMap_apply, F.negativeOutput_zero t (F.negative_zero_at_positive_level i t ht) z,
    sub_zero]
  exact centeredSynthesis_at_level _ F.positive.monotone F.positive.bounds z.val.1
    z.center _ i t ht

theorem synthesize_at_negative_level (F : InseparablePair K ι κ) (z : TwoProfile ι κ)
    (j : κ) (t : K) (ht : t ∈ F.negative.levels j) :
    (F.synthesize z).val t ≤ z.val.2.val j - 1 := by
  change F.synthesizeMap z t ≤ z.val.2.val j - 1
  rw [synthesizeMap_apply, F.positiveOutput_zero t (F.positive_zero_at_negative_level j t ht) z]
  have h := centeredSynthesis_at_level F.negative.functions F.negative.monotone F.negative.bounds
    z.val.2 (-z.center) (by have hc := z.center_bounds.2.2.2; linarith) j t ht
  change 1 - z.val.2.val j ≤ -z.center + F.negativeOutput z t at h
  linarith

theorem analyze_synthesize_le (F : InseparablePair K ι κ) (z : TwoProfile ι κ) :
    F.levels.analyze (F.synthesize z) ≤ z :=
  F.levels.analyze_le_of_bounds (F.synthesize z) z (F.synthesize_at_positive_level z)
    (F.synthesize_at_negative_level z)

/-- The final map for an already constructed inseparable pair. -/
noncomputable def ballMap (F : InseparablePair K ι κ) : UnitBall C(K, ℝ) → UnitBall C(K, ℝ) :=
  fun f => F.synthesize (F.levels.analyze f).delay

theorem ballMap_nonexpansive (F : InseparablePair K ι κ) : LipschitzWith 1 F.ballMap :=
  nonexpansive_transfer F.levels.analyze F.synthesize TwoProfile.delay
    F.levels.analyze_nonexpansive F.synthesize_nonexpansive TwoProfile.delay_nonexpansive

theorem ballMap_fixedPointFree [WellFoundedLT ι] [WellFoundedLT κ]
    (F : InseparablePair K ι κ) (f : UnitBall C(K, ℝ)) : F.ballMap f ≠ f :=
  fixedPointFree_of_order_domination F.levels.analyze F.synthesize TwoProfile.delay
    F.analyze_synthesize_le TwoProfile.no_subsolution f

theorem not_hasBFPP [WellFoundedLT ι] [WellFoundedLT κ]
    (F : InseparablePair K ι κ) : ¬ HasBFPP C(K, ℝ) :=
  not_hasBFPP_of_fixedPointFree F.ballMap F.ballMap_nonexpansive F.ballMap_fixedPointFree

end InseparablePair
end BFPP
