import BFPP.ContinuousBall

/-! # BFPP implies the F-space property

The definition uses the standard separation characterization: disjoint cozero
sets of real continuous functions have disjoint closures.
-/

namespace BFPP

set_option autoImplicit false

open Set

universe u

def IsFSpace (K : Type u) [TopologicalSpace K] : Prop :=
  ∀ f g : C(K, ℝ), Disjoint {t | f t ≠ 0} {t | g t ≠ 0} →
    Disjoint (closure {t | f t ≠ 0}) (closure {t | g t ≠ 0})

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

theorem continuous_sign_of_hasBFPP (hB : HasBFPP C(K, ℝ)) (h : C(K, ℝ)) :
    ∃ s : UnitBall C(K, ℝ),
      (∀ t, 0 < h t → s.val t = 1) ∧ (∀ t, h t < 0 → s.val t = -1) := by
  let M : ℝ := max 1 ‖h‖
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let hn : C(K, ℝ) := ⟨fun t => h t / M, h.continuous.div_const M⟩
  have hhn : ∀ t, |hn t| ≤ 1 := by
    intro t
    change |h t / M| ≤ 1
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    have ht : |h t| ≤ ‖h‖ := by
      simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm t
    exact ht.trans (le_max_right _ _)
  obtain ⟨s, hs⟩ := hB (signStep hn hhn) (signStep_nonexpansive hn hhn)
  refine ⟨s, ?_, ?_⟩
  · intro t ht
    exact signStep_fixedPoint_positive hn hhn s hs t (div_pos ht hM)
  · intro t ht
    exact signStep_fixedPoint_negative hn hhn s hs t (div_neg_of_neg_of_pos ht hM)

theorem isFSpace_of_hasBFPP (hB : HasBFPP C(K, ℝ)) : IsFSpace K := by
  intro f g hfg
  let h : C(K, ℝ) := ⟨fun t => |f t| - |g t|, by fun_prop⟩
  obtain ⟨s, hsp, hsn⟩ := continuous_sign_of_hasBFPP hB h
  have hfsub : {t | f t ≠ 0} ⊆ {t | s.val t = 1} := by
    intro t ht
    have hg : g t = 0 := by
      by_contra hg
      exact Set.disjoint_left.mp hfg ht hg
    apply hsp t
    change 0 < |f t| - |g t|
    simpa only [hg, abs_zero, sub_zero] using abs_pos.mpr ht
  have hgsub : {t | g t ≠ 0} ⊆ {t | s.val t = -1} := by
    intro t ht
    have hf : f t = 0 := by
      by_contra hf
      exact Set.disjoint_left.mp hfg hf ht
    apply hsn t
    change |f t| - |g t| < 0
    simpa only [hf, abs_zero, zero_sub, neg_lt_zero] using abs_pos.mpr ht
  have hfclosed : IsClosed {t | s.val t = 1} :=
    isClosed_eq s.val.continuous continuous_const
  have hgclosed : IsClosed {t | s.val t = -1} :=
    isClosed_eq s.val.continuous continuous_const
  apply Set.disjoint_left.mpr
  intro t ht ht'
  have hp : s.val t = 1 := closure_minimal hfsub hfclosed ht
  have hn : s.val t = -1 := closure_minimal hgsub hgclosed ht'
  linarith

end BFPP
