import BFPP.PositiveSynthesis
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! # The Radon measures representing positive synthesis -/

namespace BFPP

set_option autoImplicit false
open Set Order MeasureTheory
open scoped ZeroAtInfty CompactlySupported ENNReal

universe u v
variable {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]
  [MeasurableSpace ι] [BorelSpace ι]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K]

local instance synthesisIndexWeaklyLocallyCompact : WeaklyLocallyCompactSpace ι where
  exists_compact_mem_nhds i := ⟨Iic i, initialSegment_isCompact i,
    (initialSegment_isClopen i).isOpen.mem_nhds le_rfl⟩

noncomputable def initialStepCompact (i : ι) : C_c(ι, ℝ) where
  toFun := initialStep i
  continuous_toFun := (initialStep i).continuous
  hasCompactSupport' := (initialSegment_isCompact i).of_isClosed_subset isClosed_closure
    (closure_minimal (by
      intro j hj
      by_contra h
      change ¬ j ≤ i at h
      exact hj (by simp only [initialStep_apply, if_neg h])) isClosed_Iic)

@[simp] theorem initialStepCompact_toC0 (i : ι) :
    (initialStepCompact i : C₀(ι, ℝ)) = initialStep i := by ext; rfl

noncomputable def synthesisFunctional (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : C_c(ι, ℝ) →ₚ[ℝ] ℝ where
  toFun f := synthesisOperator w (f : C₀(ι, ℝ)) t
  map_add' f g := by
    change synthesisOperator w ((f : C₀(ι, ℝ)) + (g : C₀(ι, ℝ))) t = _
    simp only [map_add, ContinuousMap.add_apply]
  map_smul' c f := by
    change synthesisOperator w (c • (f : C₀(ι, ℝ))) t = _
    simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  monotone' f g hfg := by
    have h := synthesisOperator_positive w hw hb stepCombination_denseRange
      ((g : C₀(ι, ℝ)) - (f : C₀(ι, ℝ))) (fun i => sub_nonneg.mpr (hfg i)) t
    simpa only [map_sub, ContinuousMap.sub_apply, sub_nonneg] using h

noncomputable def synthesisMeasure (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : Measure ι := RealRMK.rieszMeasure (synthesisFunctional w hw hb t)

instance synthesisMeasure_regular (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : (synthesisMeasure w hw hb t).Regular := RealRMK.regular_rieszMeasure _

theorem synthesisFunctional_initialStep (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) (i : ι) : synthesisFunctional w hw hb t (initialStepCompact i) = w i t := by
  change synthesisOperator w (initialStepCompact i : C₀(ι, ℝ)) t = _
  rw [initialStepCompact_toC0, synthesisOperator_initialStep w hw hb stepCombination_denseRange]

theorem synthesisMeasure_initialSegment (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) (i : ι) : synthesisMeasure w hw hb t (Iic i) = ENNReal.ofReal (w i t) := by
  rw [← synthesisFunctional_initialStep w hw hb t i]
  apply le_antisymm
  · apply RealRMK.rieszMeasure_le_of_eq_one _ (f := initialStepCompact i)
      (fun j => by change 0 ≤ initialStep i j; simp only [initialStep_apply]; split_ifs <;> norm_num)
      (initialSegment_isCompact i)
    intro j hj
    change j ≤ i at hj
    change initialStep i j = 1
    simp [initialStep_apply, hj]
  · apply RealRMK.le_rieszMeasure_tsupport_subset _ (f := initialStepCompact i)
      (fun j => by
        change 0 ≤ initialStep i j ∧ initialStep i j ≤ 1
        simp only [initialStep_apply]
        split_ifs <;> norm_num)
    apply closure_minimal _ isClosed_Iic
    intro j hj
    by_contra h
    change ¬ j ≤ i at h
    exact hj (by change initialStep i j = 0; simp only [initialStep_apply, if_neg h])

/-- Inner regularity, rather than continuity of measure for an uncountable union. -/
theorem synthesisMeasure_mass (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : synthesisMeasure w hw hb t univ = ⨆ i, ENNReal.ofReal (w i t) := by
  apply le_antisymm
  · rw [isOpen_univ.measure_eq_iSup_isCompact]
    refine iSup_le fun s => iSup_le fun _ => iSup_le fun hs => ?_
    obtain ⟨i, hi⟩ := hs.bddAbove
    exact (measure_mono hi).trans ((synthesisMeasure_initialSegment w hw hb t i).le.trans
      (le_iSup (fun j => ENNReal.ofReal (w j t)) i))
  · refine iSup_le fun i => ?_
    rw [← synthesisMeasure_initialSegment w hw hb t i]
    exact measure_mono (subset_univ _)

theorem synthesisMeasure_mass_le_one (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : synthesisMeasure w hw hb t univ ≤ 1 := by
  rw [synthesisMeasure_mass]
  exact iSup_le fun i => (ENNReal.ofReal_le_ofReal (hb i t).2).trans_eq ENNReal.ofReal_one

instance synthesisMeasure_finite (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) : IsFiniteMeasure (synthesisMeasure w hw hb t) :=
  ⟨(synthesisMeasure_mass_le_one w hw hb t).trans_lt (by simp)⟩

theorem synthesisMeasure_integral_compact (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (t : K) (f : C_c(ι, ℝ)) :
    ∫ i, f i ∂synthesisMeasure w hw hb t = synthesisOperator w (f : C₀(ι, ℝ)) t :=
  RealRMK.integral_rieszMeasure (synthesisFunctional w hw hb t) f

end BFPP
