import BFPP.PositiveSynthesis

/-! # Sharp estimates for the centered synthesis channel

These proofs use positivity and uniform approximation. They do not require
representing measures to prove the contraction estimate.
-/

namespace BFPP

set_option autoImplicit false

open Set Order
open scoped ZeroAtInfty

universe u v
variable {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K]

theorem centeredSynthesis_bounds (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) (hc' : -1 ≤ c ∧ c ≤ 1) (t : K) :
    -1 ≤ c + synthesisOperator w (a.positiveTail c hc) t ∧
      c + synthesisOperator w (a.positiveTail c hc) t ≤ 1 := by
  have hpoint : ∀ i, -1 - c ≤ a.positiveTail c hc i ∧ a.positiveTail c hc i ≤ 1 - c := by
    intro i
    constructor
    · linarith [a.positiveTail_nonneg c hc i]
    · have h := a.positiveTail_le c hc i
      simpa only [max_eq_left (sub_nonneg.mpr hc'.2)] using h
  have h := synthesisOperator_preserves_bounds w hw hb stepCombination_denseRange
    (a.positiveTail c hc) (-1 - c) (1 - c) (by linarith [hc'.1])
    (by linarith [hc'.2]) hpoint t
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem centeredSynthesis_dist (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (a b : Profile ι) (c d : ℝ) (hc : 1 - a.tail ≤ c) (hd : 1 - b.tail ≤ d)
    (r : ℝ) (hab : dist a b ≤ r) (hcd : |c - d| ≤ r) (t : K) :
    |(c + synthesisOperator w (a.positiveTail c hc) t) -
      (d + synthesisOperator w (b.positiveTail d hd) t)| ≤ r := by
  let f : C₀(ι, ℝ) := a.positiveTail c hc - b.positiveTail d hd
  have hdelta := abs_le.mp hcd
  have hpoint : ∀ i, -r - (c - d) ≤ f i ∧ f i ≤ r - (c - d) := by
    intro i
    have h := abs_le.mp (Profile.center_add_positiveTail_dist a b c d hc hd r hab hcd i)
    change -r - (c - d) ≤ a.positiveTail c hc i - b.positiveTail d hd i ∧
      a.positiveTail c hc i - b.positiveTail d hd i ≤ r - (c - d)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have h := synthesisOperator_preserves_bounds w hw hb stepCombination_denseRange
    f (-r - (c - d)) (r - (c - d)) (by linarith [hdelta.1])
    (by linarith [hdelta.2]) hpoint t
  dsimp only [f] at h
  rw [map_sub] at h
  simp only [ContinuousMap.sub_apply] at h
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem centeredSynthesis_at_level (w : ι → C(K, ℝ))
    (hw : ∀ t, Monotone (fun i => w i t)) (hb : ∀ i t, 0 ≤ w i t ∧ w i t ≤ 1)
    (a : Profile ι) (c : ℝ) (hc : 1 - a.tail ≤ c) (i : ι) (t : K) (ht : w i t = 1) :
    1 - a.val i ≤ c + synthesisOperator w (a.positiveTail c hc) t := by
  have hlocal : ∀ j, j ≤ i → 1 - a.val i - c ≤ a.positiveTail c hc j := by
    intro j hji
    have h₁ := a.regularizeValue_le_apply j
    have h₂ := a.monotone hji
    have h₃ : 1 - a.regularizeValue j - c ≤ a.positiveTail c hc j := le_max_left _ _
    linarith
  have h := synthesisOperator_lower_on_initialSegment w hw hb (a.positiveTail c hc)
    (a.positiveTail_nonneg c hc) i t ht (1 - a.val i - c) hlocal
  linarith

end BFPP
