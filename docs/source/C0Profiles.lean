import BFPP.Regularization
import BFPP.Center
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FunProp

/-! # Synthesis profiles vanish at infinity -/

namespace BFPP

set_option autoImplicit false

open Set Order Filter Topology
open scoped ZeroAtInfty

universe u
variable {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]

namespace Profile

theorem regularize_tendsto_tail (a : Profile ι) :
    Tendsto a.regularizeValue atTop (𝓝 a.tail) := by
  have h := tendsto_atTop_ciSup a.regularize.monotone a.regularize.val.bddAbove_range
  change Tendsto a.regularizeValue atTop (𝓝 a.regularize.tail) at h
  rwa [tail_regularize] at h

/-- The positive-part profile used by the positive synthesis channel. -/
noncomputable def positiveTail (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) : C₀(ι, ℝ) where
  toFun i := max (1 - a.regularizeValue i - c) 0
  continuous_toFun := ((continuous_const.sub a.regularizeValue_continuous).sub
    continuous_const).max continuous_const
  zero_at_infty' := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub a.regularize_tendsto_tail).sub
      (tendsto_const_nhds (x := c))).max (tendsto_const_nhds (x := (0 : ℝ)))
    have hz : max (1 - a.tail - c) 0 = 0 := max_eq_right (by linarith)
    rw [hz] at h
    exact h.mono_left cocompact_le_atTop

@[simp] theorem positiveTail_apply (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) (i : ι) :
    a.positiveTail c hc i = max (1 - a.regularizeValue i - c) 0 := rfl

theorem positiveTail_nonneg (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) (i : ι) :
    0 ≤ a.positiveTail c hc i := le_max_right _ _

theorem positiveTail_le (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) (i : ι) :
    a.positiveTail c hc i ≤ max (1 - c) 0 := by
  apply max_le_max _ le_rfl
  have h := a.regularizeValue_nonneg i
  linarith

theorem center_add_positiveTail (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) (i : ι) :
    c + a.positiveTail c hc i = max c (1 - a.regularizeValue i) := by
  rw [positiveTail_apply]
  by_cases h : 0 ≤ 1 - a.regularizeValue i - c
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

/-- The center and the profile enter a single maximum, preserving constant one. -/
theorem center_add_positiveTail_dist (a b : Profile ι) (c d : ℝ)
    (hc : 1 - a.tail ≤ c) (hd : 1 - b.tail ≤ d) (r : ℝ)
    (hab : dist a b ≤ r) (hcd : |c - d| ≤ r) (i : ι) :
    |(c + a.positiveTail c hc i) - (d + b.positiveTail d hd i)| ≤ r := by
  rw [center_add_positiveTail, center_add_positiveTail]
  apply max_nonexpansive_bound hcd
  have h₁ := BoundedFamily.abs_sub_apply_le_dist a.regularize.val b.regularize.val i
  have h₂ := regularize_nonexpansive.dist_le_mul a b
  have h₂' : dist a.regularize b.regularize ≤ dist a b := by
    simpa only [NNReal.coe_one, one_mul] using h₂
  have h₃ : |a.regularizeValue i - b.regularizeValue i| ≤ r :=
    h₁.trans (h₂'.trans hab)
  calc
    |1 - a.regularizeValue i - (1 - b.regularizeValue i)| =
        |b.regularizeValue i - a.regularizeValue i| := by congr 1; ring
    _ = |a.regularizeValue i - b.regularizeValue i| := abs_sub_comm _ _
    _ ≤ r := h₃

end Profile
end BFPP
