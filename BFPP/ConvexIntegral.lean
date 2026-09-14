import BFPP.SynthesisIntegral
import BFPP.Realization

/-! # The convex-integral formula for the synthesis map

The two representing measures have combined mass at most one. Expanding the
constant part of each integral gives the displayed max/min formula in the paper.
-/

namespace BFPP

set_option autoImplicit false
open Set Order MeasureTheory
open scoped ZeroAtInfty

universe u v w

/-- Reallocate the constant center among two finite measures and its remaining weight. -/
theorem convexIntegral_identity {ι : Type v} {κ : Type w}
    [MeasurableSpace ι] [MeasurableSpace κ]
    (μ : Measure ι) (ν : Measure κ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ) (f : ι → ℝ) (g : κ → ℝ) (hf : Integrable f μ) (hg : Integrable g ν) :
    c + (∫ i, f i ∂μ) - (∫ j, g j ∂ν) =
      (1 - μ.real univ - ν.real univ) * c +
        (∫ i, c + f i ∂μ) + (∫ j, c - g j ∂ν) := by
  rw [integral_add (integrable_const c) hf, integral_sub (integrable_const c) hg,
    integral_const, integral_const]
  simp only [smul_eq_mul]
  ring

variable {K : Type u} {ι : Type v} {κ : Type w}
  [TopologicalSpace K] [CompactSpace K]
  [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]
  [MeasurableSpace ι] [BorelSpace ι]
  [LinearOrder κ] [OrderBot κ] [SuccOrder κ] [NoMaxOrder κ]
  [TopologicalSpace κ] [OrderTopology κ] [CompactIccSpace κ]
  [MeasurableSpace κ] [BorelSpace κ]

namespace InseparablePair

noncomputable abbrev positiveMeasure (F : InseparablePair K ι κ) (t : K) : Measure ι :=
  synthesisMeasure F.positive.functions F.positive.monotone F.positive.bounds t

noncomputable abbrev negativeMeasure (F : InseparablePair K ι κ) (t : K) : Measure κ :=
  synthesisMeasure F.negative.functions F.negative.monotone F.negative.bounds t

/-- Orthogonality forces one of the two total masses to vanish at each point. -/
theorem synthesisMass_zero_or_zero (F : InseparablePair K ι κ) (t : K) :
    (F.positiveMeasure t).real univ = 0 ∨ (F.negativeMeasure t).real univ = 0 := by
  rcases F.disjoint_channels t with hp | hn
  · left
    rw [synthesisMeasure_real_mass]
    simp [hp]
  · right
    rw [synthesisMeasure_real_mass]
    simp [hn]

omit [SuccOrder κ] [NoMaxOrder κ] [TopologicalSpace κ] [OrderTopology κ]
  [CompactIccSpace κ] [MeasurableSpace κ] [BorelSpace κ] in
theorem positiveMass_le_one (F : InseparablePair K ι κ) (t : K) :
    (F.positiveMeasure t).real univ ≤ 1 := by
  rw [synthesisMeasure_real_mass]
  exact ciSup_le fun i => (F.positive.bounds i t).2

omit [SuccOrder ι] [NoMaxOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [CompactIccSpace ι] [MeasurableSpace ι] [BorelSpace ι] in
theorem negativeMass_le_one (F : InseparablePair K ι κ) (t : K) :
    (F.negativeMeasure t).real univ ≤ 1 := by
  rw [synthesisMeasure_real_mass]
  exact ciSup_le fun j => (F.negative.bounds j t).2

/-- The two measures and the residual atom form a probability weighting. -/
theorem synthesisMass_add_le_one (F : InseparablePair K ι κ) (t : K) :
    (F.positiveMeasure t).real univ + (F.negativeMeasure t).real univ ≤ 1 := by
  rcases F.synthesisMass_zero_or_zero t with hp | hn
  · simpa only [hp, zero_add] using F.negativeMass_le_one t
  · simpa only [hn, add_zero] using F.positiveMass_le_one t

theorem synthesisResidualWeight_nonneg (F : InseparablePair K ι κ) (t : K) :
    0 ≤ 1 - (F.positiveMeasure t).real univ - (F.negativeMeasure t).real univ := by
  linarith [F.synthesisMass_add_le_one t]

theorem synthesizeMap_convexIntegral (F : InseparablePair K ι κ) (z : TwoProfile ι κ)
    (t : K) :
    F.synthesizeMap z t =
      (1 - (F.positiveMeasure t).real univ - (F.negativeMeasure t).real univ) * z.center +
        (∫ i, z.center + positiveInput z i ∂F.positiveMeasure t) +
        (∫ j, z.center - negativeInput z j ∂F.negativeMeasure t) := by
  rw [synthesizeMap_apply]
  change z.center + synthesisOperator F.positive.functions (positiveInput z) t -
    synthesisOperator F.negative.functions (negativeInput z) t = _
  rw [← synthesisMeasure_integral F.positive.functions F.positive.monotone F.positive.bounds,
    ← synthesisMeasure_integral F.negative.functions F.negative.monotone F.negative.bounds]
  exact convexIntegral_identity (F.positiveMeasure t) (F.negativeMeasure t) z.center
    (positiveInput z) (negativeInput z) ((positiveInput z).toBCF.integrable _)
    ((negativeInput z).toBCF.integrable _)

omit [MeasurableSpace ι] [BorelSpace ι] [SuccOrder κ] [NoMaxOrder κ]
  [TopologicalSpace κ] [OrderTopology κ] [CompactIccSpace κ] [MeasurableSpace κ]
  [BorelSpace κ] in
theorem center_add_positiveInput (z : TwoProfile ι κ) (i : ι) :
    z.center + positiveInput z i = max z.center (1 - z.val.1.regularizeValue i) :=
  Profile.center_add_positiveTail _ _ _ _

omit [SuccOrder ι] [NoMaxOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [CompactIccSpace ι] [MeasurableSpace ι] [BorelSpace ι] [MeasurableSpace κ]
  [BorelSpace κ] in
theorem center_sub_negativeInput (z : TwoProfile ι κ) (j : κ) :
    z.center - negativeInput z j = min z.center (z.val.2.regularizeValue j - 1) := by
  change z.center - max (1 - z.val.2.regularizeValue j - -z.center) 0 = _
  rw [sub_neg_eq_add]
  by_cases h : 0 ≤ 1 - z.val.2.regularizeValue j + z.center
  · rw [max_eq_left h, min_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge h), min_eq_left (by linarith), sub_zero]

/-- The paper's displayed convex-integral synthesis formula, with its actual measures. -/
theorem synthesizeMap_convexIntegral_max_min (F : InseparablePair K ι κ)
    (z : TwoProfile ι κ) (t : K) :
    F.synthesizeMap z t =
      (1 - (F.positiveMeasure t).real univ - (F.negativeMeasure t).real univ) * z.center +
        (∫ i, max z.center (1 - z.val.1.regularizeValue i) ∂F.positiveMeasure t) +
        (∫ j, min z.center (z.val.2.regularizeValue j - 1) ∂F.negativeMeasure t) := by
  simpa only [center_add_positiveInput, center_sub_negativeInput] using
    F.synthesizeMap_convexIntegral z t

omit [SuccOrder κ] [NoMaxOrder κ] [TopologicalSpace κ] [OrderTopology κ]
  [CompactIccSpace κ] [MeasurableSpace κ] [BorelSpace κ] in
theorem positiveIntegrand_integrable (F : InseparablePair K ι κ)
    (z : TwoProfile ι κ) (t : K) :
    Integrable (fun i => max z.center (1 - z.val.1.regularizeValue i))
      (F.positiveMeasure t) := by
  have h : Integrable (fun i => z.center + positiveInput z i) (F.positiveMeasure t) :=
    (integrable_const z.center).add ((positiveInput z).toBCF.integrable (F.positiveMeasure t))
  simpa only [center_add_positiveInput] using h

omit [SuccOrder ι] [NoMaxOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [CompactIccSpace ι] [MeasurableSpace ι] [BorelSpace ι] in
theorem negativeIntegrand_integrable (F : InseparablePair K ι κ)
    (z : TwoProfile ι κ) (t : K) :
    Integrable (fun j => min z.center (z.val.2.regularizeValue j - 1))
      (F.negativeMeasure t) := by
  have h : Integrable (fun j => z.center - negativeInput z j) (F.negativeMeasure t) :=
    (integrable_const z.center).sub ((negativeInput z).toBCF.integrable (F.negativeMeasure t))
  simpa only [center_sub_negativeInput] using h

end InseparablePair
end BFPP
