import BFPP.C0Profiles
import BFPP.FiniteSynthesis
import Mathlib.Topology.Algebra.Indicator
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Compactly supported initial-segment functions -/

namespace BFPP

set_option autoImplicit false

open Set Order Filter Topology
open scoped ZeroAtInfty

universe u
variable {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]

theorem initialSegment_isClopen (i : ι) : IsClopen (Iic i) := by
  refine ⟨isClosed_Iic, ?_⟩
  have he : Iic i = Iio (Order.succ i) := by ext j; simp only [mem_Iic, mem_Iio, Order.lt_succ_iff]
  rw [he]
  exact isOpen_Iio

theorem initialSegment_isCompact (i : ι) : IsCompact (Iic i) := by
  simpa only [Icc_bot] using (isCompact_Icc (a := (⊥ : ι)) (b := i))

noncomputable def initialStep (i : ι) : C₀(ι, ℝ) where
  toFun := (Iic i).indicator (fun _ => 1)
  continuous_toFun := (initialSegment_isClopen i).continuous_indicator continuous_const
  zero_at_infty' := by
    have he : (fun _ : ι => (0 : ℝ)) =ᶠ[cocompact ι] (Iic i).indicator (fun _ => 1) := by
      filter_upwards [(initialSegment_isCompact i).compl_mem_cocompact] with j hj
      simp only [Set.indicator_of_notMem hj]
    exact tendsto_const_nhds.congr' he

@[simp] theorem initialStep_apply (i j : ι) : initialStep i j = if j ≤ i then 1 else 0 := by
  classical
  change (Iic i).indicator (fun _ => (1 : ℝ)) j = _
  by_cases h : j ≤ i <;> simp [Set.indicator, h]

noncomputable def c0Eval (i : ι) : C₀(ι, ℝ) →ₗ[ℝ] ℝ where
  toFun f := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem c0_abs_apply_le_norm (f : C₀(ι, ℝ)) (i : ι) : |f i| ≤ ‖f‖ := by
  change ‖f.toBCF i‖ ≤ ‖f.toBCF‖
  exact f.toBCF.norm_coe_le_norm i

theorem c0_norm_le (f : C₀(ι, ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, |f i| ≤ C) : ‖f‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC).mpr hf

theorem c0_abs_sub_le_dist (f g : C₀(ι, ℝ)) (i : ι) : |f i - g i| ≤ dist f g := by
  rw [dist_eq_norm]
  exact c0_abs_apply_le_norm (f - g) i

noncomputable def stepCombination : (ι →₀ ℝ) →ₗ[ℝ] C₀(ι, ℝ) :=
  Finsupp.linearCombination ℝ initialStep

theorem stepCombination_apply (c : ι →₀ ℝ) (i : ι) :
    stepCombination c i = stepFinsetValue c.support c i := by
  change c0Eval i (Finsupp.linearCombination ℝ initialStep c) = _
  rw [Finsupp.apply_linearCombination]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply,
    c0Eval, LinearMap.coe_mk, AddHom.coe_mk, initialStep_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, stepFinsetValue]

@[simp] theorem stepCombination_single (i : ι) :
    stepCombination (Finsupp.single i (1 : ℝ)) = initialStep i := by
  simp [stepCombination, Finsupp.linearCombination_single]

end BFPP
