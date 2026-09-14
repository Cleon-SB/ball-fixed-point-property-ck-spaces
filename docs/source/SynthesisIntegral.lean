import BFPP.SynthesisMeasure

/-! # Representation on all of C₀ by continuity and step-function density -/

namespace BFPP

set_option autoImplicit false
open Set Order MeasureTheory
open scoped ZeroAtInfty CompactlySupported

universe u v
variable {ι : Type u} [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]

noncomputable def c0IntegralLinear (μ : Measure ι) [IsFiniteMeasure μ] : C₀(ι, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ i, f i ∂μ
  map_add' f g := integral_add (f.toBCF.integrable μ) (g.toBCF.integrable μ)
  map_smul' c f := by simpa using integral_smul c (fun i => f i)

noncomputable def c0Integral (μ : Measure ι) [IsFiniteMeasure μ] : C₀(ι, ℝ) →L[ℝ] ℝ :=
  (c0IntegralLinear μ).mkContinuous (μ.real univ)
    (fun f => f.toBCF.norm_integral_le_mul_norm μ)

variable [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [OrderTopology ι] [CompactIccSpace ι]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K]

theorem synthesisMeasure_integral (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) (f : C₀(ι, ℝ)) :
    ∫ i, f i ∂synthesisMeasure w hw hb t = synthesisOperator w f t := by
  change c0Integral (synthesisMeasure w hw hb t) f = synthesisOperator w f t
  refine stepCombination_denseRange.induction_on f ?_ ?_
  · exact isClosed_eq (c0Integral _).continuous
      ((ContinuousMap.evalCLM ℝ t).continuous.comp (synthesisOperator w).continuous)
  · intro c
    rw [stepCombination_eq_sum, map_sum, map_sum, ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul, ContinuousMap.smul_apply]
    congr 1
    exact synthesisMeasure_integral_compact w hw hb t (initialStepCompact i)

/-- Full measure conclusion of the positive-synthesis lemma. -/
theorem synthesisMeasure_real_mass (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : (synthesisMeasure w hw hb t).real univ = ⨆ i, w i t := by
  change (synthesisMeasure w hw hb t univ).toReal = _
  rw [synthesisMeasure_mass, ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  apply iSup_congr
  intro i
  exact ENNReal.toReal_ofReal (hb i t).1

/-- Full measure conclusion of the positive-synthesis lemma. -/
theorem positiveSynthesis_measure_representation (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : ∃ μ : Measure ι, μ.Regular ∧ IsFiniteMeasure μ ∧
      (∀ f : C₀(ι, ℝ), ∫ i, f i ∂μ = synthesisOperator w f t) ∧
      (∀ i, μ (Iic i) = ENNReal.ofReal (w i t)) ∧
      μ univ = ⨆ i, ENNReal.ofReal (w i t) ∧ μ univ ≤ 1 :=
  ⟨synthesisMeasure w hw hb t, inferInstance, inferInstance,
    synthesisMeasure_integral w hw hb t, synthesisMeasure_initialSegment w hw hb t,
    synthesisMeasure_mass w hw hb t, synthesisMeasure_mass_le_one w hw hb t⟩

end BFPP
