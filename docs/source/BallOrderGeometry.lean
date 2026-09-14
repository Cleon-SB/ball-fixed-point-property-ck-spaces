import BFPP.ContinuousBall
import Mathlib.Topology.ContinuousMap.Ordered

/-! # Order intervals and metric balls in the continuous-function unit ball -/

namespace BFPP

set_option autoImplicit false
open Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem continuousBall_dist_le_iff (f g : UnitBall C(K, ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ t, |f.val t - g.val t| ≤ r := by
  change dist f.val g.val ≤ r ↔ _
  simpa only [Real.dist_eq] using (ContinuousMap.dist_le (f := f.val) (g := g.val) hr)

noncomputable def ballLower (f : UnitBall C(K, ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    UnitBall C(K, ℝ) := by
  let g : C(K, ℝ) := ⟨fun t => max (-1) (f.val t - r), by fun_prop⟩
  refine ⟨g, (ContinuousMap.norm_le _ (by norm_num)).mpr ?_⟩
  intro t
  change |max (-1) (f.val t - r)| ≤ 1
  have ht := continuousBall_bounds f t
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (by linarith [ht.2])⟩

noncomputable def ballUpper (f : UnitBall C(K, ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    UnitBall C(K, ℝ) := by
  let g : C(K, ℝ) := ⟨fun t => min 1 (f.val t + r), by fun_prop⟩
  refine ⟨g, (ContinuousMap.norm_le _ (by norm_num)).mpr ?_⟩
  intro t
  change |min 1 (f.val t + r)| ≤ 1
  have ht := continuousBall_bounds f t
  exact abs_le.mpr ⟨le_min (by norm_num) (by linarith [ht.1]), min_le_left _ _⟩

theorem continuousBall_closedBall_eq_Icc (f : UnitBall C(K, ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall f r = Icc (ballLower f r hr) (ballUpper f r hr) := by
  ext g
  simp only [Metric.mem_closedBall, continuousBall_dist_le_iff _ _ r hr, mem_Icc]
  constructor
  · intro h
    constructor <;> intro t
    · change max (-1) (f.val t - r) ≤ g.val t
      exact max_le (continuousBall_bounds g t).1 (by linarith [(abs_le.mp (h t)).1])
    · change g.val t ≤ min 1 (f.val t + r)
      exact le_min (continuousBall_bounds g t).2 (by linarith [(abs_le.mp (h t)).2])
  · intro h t
    have hlo := h.1 t
    have hup := h.2 t
    change max (-1) (f.val t - r) ≤ g.val t at hlo
    change g.val t ≤ min 1 (f.val t + r) at hup
    have hl := (le_max_right _ _).trans hlo
    have hu := hup.trans (min_le_right _ _)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def continuousBallMidpoint (l u : UnitBall C(K, ℝ)) : UnitBall C(K, ℝ) := by
  let m : C(K, ℝ) := ⟨fun t => (l.val t + u.val t) / 2, by fun_prop⟩
  refine ⟨m, (ContinuousMap.norm_le _ (by norm_num)).mpr ?_⟩
  intro t
  change |(l.val t + u.val t) / 2| ≤ 1
  have hl := continuousBall_bounds l t
  have hu := continuousBall_bounds u t
  exact abs_le.mpr ⟨by linarith [hl.1, hu.1], by linarith [hl.2, hu.2]⟩

theorem continuousBall_midpoint_radius (l u : UnitBall C(K, ℝ)) (hlu : l ≤ u) :
    ∃ m ∈ Icc l u, ∀ z ∈ Icc l u, dist m z ≤ dist l u / 2 := by
  refine ⟨continuousBallMidpoint l u, ?_, ?_⟩
  · constructor
    · intro t
      change l.val t ≤ (l.val t + u.val t) / 2
      have ht : l.val t ≤ u.val t := hlu t
      linarith
    · intro t
      change (l.val t + u.val t) / 2 ≤ u.val t
      have ht : l.val t ≤ u.val t := hlu t
      linarith
  · intro z hz
    apply (continuousBall_dist_le_iff _ _ _ (by positivity)).mpr
    intro t
    change |(l.val t + u.val t) / 2 - z.val t| ≤ dist l u / 2
    have hdist := continuousMap_abs_sub_le_dist l.val u.val t
    change |l.val t - u.val t| ≤ dist l u at hdist
    have hd := (abs_le.mp hdist).1
    have hl := hz.1 t
    have hu := hz.2 t
    change l.val t ≤ z.val t at hl
    change z.val t ≤ u.val t at hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end BFPP
