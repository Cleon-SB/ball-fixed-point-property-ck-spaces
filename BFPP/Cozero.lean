import BFPP.FSpaceNecessary
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Countable unions of cozero sets -/

namespace BFPP

set_option autoImplicit false

open Set

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

noncomputable def normalizedAbs (f : C(K, ℝ)) : C(K, ℝ) :=
  ⟨fun t => |f t| / (1 + ‖f‖), by fun_prop⟩

theorem normalizedAbs_bounds (f : C(K, ℝ)) (t : K) :
    0 ≤ normalizedAbs f t ∧ normalizedAbs f t ≤ 1 := by
  have hd : 0 < 1 + ‖f‖ := by linarith [norm_nonneg f]
  constructor
  · exact div_nonneg (abs_nonneg _) hd.le
  · change |f t| / (1 + ‖f‖) ≤ 1
    rw [div_le_one hd]
    have h : |f t| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm t
    linarith

theorem normalizedAbs_norm_le (f : C(K, ℝ)) : ‖normalizedAbs f‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (normalizedAbs_bounds f t).1]
  exact (normalizedAbs_bounds f t).2

@[simp] theorem normalizedAbs_eq_zero (f : C(K, ℝ)) (t : K) :
    normalizedAbs f t = 0 ↔ f t = 0 := by
  have hd : 1 + ‖f‖ ≠ 0 := ne_of_gt (by linarith [norm_nonneg f])
  change |f t| / (1 + ‖f‖) = 0 ↔ f t = 0
  simp [div_eq_zero_iff, hd]

theorem countable_union_cozero (f : ℕ → C(K, ℝ)) :
    ∃ g : C(K, ℝ), {t | g t ≠ 0} = ⋃ n, {t | f n t ≠ 0} := by
  let term : ℕ → C(K, ℝ) := fun n => (1 / 2 : ℝ) ^ n • normalizedAbs (f n)
  have hp (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hterm (n : ℕ) : ‖term n‖ ≤ (1 / 2 : ℝ) ^ n := by
    dsimp only [term]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hp n)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (normalizedAbs_norm_le (f n)) (hp n).le
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hs : Summable term := hgeo.of_norm_bounded hterm
  let g : C(K, ℝ) := ∑' n, term n
  have hnonneg (n : ℕ) (t : K) : 0 ≤ term n t :=
    mul_nonneg (hp n).le (normalizedAbs_bounds (f n) t).1
  have hzero (t : K) : g t = 0 ↔ ∀ n, f n t = 0 := by
    have hseval := (ContinuousMap.evalCLM ℝ t).summable hs
    have heval : g t = ∑' n, term n t := (ContinuousMap.evalCLM ℝ t).map_tsum hs
    constructor
    · intro hg n
      have hle : term n t ≤ ∑' k, term k t := by
        simpa only [Finset.sum_singleton] using
          hseval.sum_le_tsum {n} (fun k _hk => hnonneg k t)
      rw [← heval, hg] at hle
      have hz : term n t = 0 := le_antisymm hle (hnonneg n t)
      change (1 / 2 : ℝ) ^ n * normalizedAbs (f n) t = 0 at hz
      exact (normalizedAbs_eq_zero (f n) t).mp
        ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (hp n)))
    · intro h
      rw [heval]
      have hz : ∀ n, term n t = 0 := by
        intro n
        change (1 / 2 : ℝ) ^ n * normalizedAbs (f n) t = 0
        rw [(normalizedAbs_eq_zero (f n) t).mpr (h n), mul_zero]
      simp only [hz, tsum_zero]
  refine ⟨g, ?_⟩
  ext t
  simp only [Set.mem_ofPred_eq, mem_iUnion, ne_eq, hzero, not_forall]

end BFPP
