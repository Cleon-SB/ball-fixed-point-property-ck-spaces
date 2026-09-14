import BFPP.Cozero
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Sets.Closeds

/-! # Sign extension and the fresh-value argument -/

namespace BFPP

set_option autoImplicit false

open Set TopologicalSpace

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

theorem exists_sign_extension [NormalSpace K] (U V : Set K)
    (hUV : Disjoint (closure U) (closure V)) :
    ∃ h : UnitBall C(K, ℝ), (∀ t ∈ closure U, h.val t = 1) ∧
      (∀ t ∈ closure V, h.val t = -1) := by
  obtain ⟨f, hfV, hfU, hf⟩ := exists_continuous_zero_one_of_isClosed
    isClosed_closure isClosed_closure hUV.symm
  let h : C(K, ℝ) := ⟨fun t => 2 * f t - 1, by fun_prop⟩
  have hnorm : ‖h‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num)).mpr
    intro t
    change |2 * f t - 1| ≤ 1
    have ht := hf t
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨⟨h, hnorm⟩, ?_, ?_⟩
  · intro t ht
    change 2 * f t - 1 = 1
    have he : f t = 1 := hfU ht
    rw [he]
    norm_num
  · intro t ht
    change 2 * f t - 1 = -1
    have he : f t = 0 := hfV ht
    rw [he]
    norm_num

theorem IsFSpace.disjoint_sign_closures (hK : IsFSpace K) (h : C(K, ℝ)) :
    Disjoint (closure {t | 0 < h t}) (closure {t | h t < 0}) := by
  let p : C(K, ℝ) := ⟨fun t => max (h t) 0, h.continuous.max continuous_const⟩
  let n : C(K, ℝ) := ⟨fun t => max (-h t) 0, h.continuous.neg.max continuous_const⟩
  have hp : {t | p t ≠ 0} = {t | 0 < h t} := by
    ext t
    change max (h t) 0 ≠ 0 ↔ 0 < h t
    simp only [ne_eq, max_eq_right_iff, not_le]
  have hn : {t | n t ≠ 0} = {t | h t < 0} := by
    ext t
    change max (-h t) 0 ≠ 0 ↔ h t < 0
    simp only [ne_eq, max_eq_right_iff, not_le, neg_pos]
  have hd : Disjoint {t | p t ≠ 0} {t | n t ≠ 0} := by
    rw [hp, hn]
    apply Set.disjoint_left.mpr
    intro t ht ht'
    change 0 < h t at ht
    change h t < 0 at ht'
    linarith
  have hd' := hK p n hd
  simpa only [hp, hn] using hd'

/-- The ordered pair of points cannot be separated by a clopen set. -/
def ClopenInseparable (p q : K) : Prop := ∀ s : Clopens K, p ∈ s → q ∈ s

theorem exists_intermediate_value_of_clopenInseparable (p q : K)
    (hpq : ClopenInseparable p q) (h : UnitBall C(K, ℝ))
    (hp : h.val p = 1) (hq : h.val q = -1) :
    ∃ t, 0 < |h.val t| ∧ |h.val t| < 1 := by
  by_contra hnone
  have heq : ∀ t, 0 < h.val t → h.val t = 1 := by
    intro t ht
    have hl : 1 ≤ |h.val t| := by
      by_contra hl
      exact hnone ⟨t, by simpa only [abs_of_pos ht] using ht, lt_of_not_ge hl⟩
    rw [abs_of_pos ht] at hl
    exact le_antisymm (continuousBall_bounds h t).2 hl
  have hset : {t | 0 < h.val t} = {t | h.val t = 1} := by
    ext t
    constructor
    · exact heq t
    · intro ht
      change 0 < h.val t
      rw [ht]
      norm_num
  have hclosed : IsClosed {t | 0 < h.val t} := by
    rw [hset]
    exact isClosed_eq h.val.continuous continuous_const
  have hopen : IsOpen {t | 0 < h.val t} := isOpen_lt continuous_const h.val.continuous
  let s : Clopens K := ⟨{t | 0 < h.val t}, hclosed, hopen⟩
  have hps : p ∈ s := by change 0 < h.val p; rw [hp]; norm_num
  have hqs := hpq s hps
  change 0 < h.val q at hqs
  rw [hq] at hqs
  norm_num at hqs

end BFPP
