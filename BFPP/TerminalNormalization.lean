import BFPP.TerminalSupremum
import BFPP.BoundedFamilies
import Mathlib.Algebra.Order.GroupWithZero.OrderIso

/-! # Normalizing a discontinuous terminal supremum -/

namespace BFPP

set_option autoImplicit false
open Set unitInterval

universe u v
variable {K : Type u} [TopologicalSpace K]

noncomputable def boundedUnitFunction (f : K → I) : BoundedFamily K :=
  BoundedFamily.ofBound (fun t => (f t : ℝ)) 1
    (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (f t).property.1]; exact (f t).property.2)

theorem terminal_norm_pos (f : K → I) (hf : ¬ Continuous f) : 0 < ‖boundedUnitFunction f‖ := by
  by_contra h
  have hzero : ‖boundedUnitFunction f‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
  have hv : ∀ t, (f t : ℝ) = 0 := by
    intro t
    have hb := (boundedUnitFunction f).abs_apply_le_norm t
    rw [hzero] at hb
    exact abs_nonpos_iff.mp hb
  have hc : Continuous (fun t => (f t : ℝ)) := by
    simp only [hv]
    exact continuous_const
  exact hf (hc.subtype_mk _)

noncomputable def normalizedTerminal (f : K → I) : BoundedFamily K :=
  ‖boundedUnitFunction f‖⁻¹ • boundedUnitFunction f

@[simp] theorem normalizedTerminal_apply (f : K → I) (t : K) :
    normalizedTerminal f t = ‖boundedUnitFunction f‖⁻¹ * (f t : ℝ) := rfl

theorem normalizedTerminal_norm (f : K → I) (hf : ¬ Continuous f) :
    ‖normalizedTerminal f‖ = 1 := by
  have hr := terminal_norm_pos f hf
  letI : TopologicalSpace K := ⊥
  rw [normalizedTerminal, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

theorem normalizedTerminal_bounds (f : K → I) (hf : ¬ Continuous f) (t : K) :
    0 ≤ normalizedTerminal f t ∧ normalizedTerminal f t ≤ 1 := by
  have hr := terminal_norm_pos f hf
  rw [normalizedTerminal_apply]
  refine ⟨mul_nonneg (inv_nonneg.mpr hr.le) (f t).property.1, ?_⟩
  have hb : (f t : ℝ) ≤ ‖boundedUnitFunction f‖ :=
    ((le_abs_self _).trans ((boundedUnitFunction f).abs_apply_le_norm t))
  calc
    ‖boundedUnitFunction f‖⁻¹ * (f t : ℝ) ≤ ‖boundedUnitFunction f‖⁻¹ * ‖boundedUnitFunction f‖ :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)
    _ = 1 := inv_mul_cancel₀ hr.ne'

theorem normalizedTerminal_not_continuous (f : K → I) (hf : ¬ Continuous f) :
    ¬ Continuous (fun t => normalizedTerminal f t) := by
  intro hc
  have he : (fun t => ‖boundedUnitFunction f‖ * normalizedTerminal f t) = fun t => (f t : ℝ) := by
    funext t
    rw [normalizedTerminal_apply, ← mul_assoc,
      mul_inv_cancel₀ (terminal_norm_pos f hf).ne', one_mul]
  have hc' : Continuous (fun t => (f t : ℝ)) := he ▸ continuous_const.mul hc
  exact hf (hc'.subtype_mk _)

/-- Positive rescaling preserves every nonempty bounded pointwise supremum,
and hence all the limit and terminal identities in the appendix. -/
theorem positive_scale_ciSup {ι : Type v} [Nonempty ι] (a : ℝ) (ha : 0 < a)
    (g : ι → ℝ) (hg : BddAbove (range g)) : a * (⨆ i, g i) = ⨆ i, a * g i :=
  (OrderIso.mulLeft₀ a ha).map_ciSup hg

theorem normalized_profile_bounds (f : K → I) (hf : ¬ Continuous f) (g : C(K, I))
    (hg : ∀ t, g t ≤ f t) (t : K) :
    0 ≤ ‖boundedUnitFunction f‖⁻¹ * (g t : ℝ) ∧
      ‖boundedUnitFunction f‖⁻¹ * (g t : ℝ) ≤ 1 := by
  have hr := (terminal_norm_pos f hf).le
  refine ⟨mul_nonneg (inv_nonneg.mpr hr) (g t).property.1, ?_⟩
  have hgt : (g t : ℝ) ≤ (f t : ℝ) := hg t
  exact (mul_le_mul_of_nonneg_left hgt (inv_nonneg.mpr hr)).trans
    (normalizedTerminal_bounds f hf t).2

theorem normalized_profile_continuous (f : K → I) (g : C(K, I)) :
    Continuous (fun t => ‖boundedUnitFunction f‖⁻¹ * (g t : ℝ)) :=
  continuous_const.mul (continuous_subtype_val.comp g.continuous)

end BFPP
