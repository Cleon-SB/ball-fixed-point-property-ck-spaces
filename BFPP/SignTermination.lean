import BFPP.SignRecursion
import Mathlib.Order.WellFounded

/-! # Termination at a limit ordinal -/

namespace BFPP

set_option autoImplicit false

open Set Order

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [NormalSpace K]

theorem signRecursion_ne_of_lt (seed : UnitBall C(K, ℝ)) (p q : K)
    (hpq : ClopenInseparable p q) (hp : seed.val p = 1) (hq : seed.val q = -1)
    (a b : Ordinal.{u}) (ha₁ : 1 ≤ a) (hab : a < b)
    (ha : SignStageGood seed a) (hb : SignStageGood seed b) :
    signRecursion seed a ≠ signRecursion seed b := by
  have hpoints := signRecursion_at_points seed p q hp hq a ha₁ ha
  obtain ⟨t, ht₀, ht₁⟩ := exists_intermediate_value_of_clopenInseparable p q hpq
    (signRecursion seed a) hpoints.1 hpoints.2
  intro heq
  have heval := congrArg (fun h : UnitBall C(K, ℝ) => h.val t) heq
  rcases lt_or_gt_of_ne (abs_pos.mp ht₀) with hneg | hpos
  · have ht := signRecursion_negative_saturated seed a b hab hb t hneg
    rw [heval, ht] at ht₁
    norm_num at ht₁
  · have ht := signRecursion_positive_saturated seed a b hab hb t hpos
    rw [heval, ht] at ht₁
    norm_num at ht₁

theorem exists_bad_signStage (seed : UnitBall C(K, ℝ)) (p q : K)
    (hpq : ClopenInseparable p q) (hp : seed.val p = 1) (hq : seed.val q = -1) :
    ∃ a : Ordinal.{u}, ¬ SignStageGood seed a := by
  by_contra hnone
  have hgood : ∀ a : Ordinal.{u}, SignStageGood seed a := by
    intro a
    by_contra ha
    exact hnone ⟨a, ha⟩
  let f : Ordinal.{u} → UnitBall C(K, ℝ) := fun a => signRecursion seed (Order.succ a)
  have hsucc (a : Ordinal.{u}) : (1 : Ordinal.{u}) ≤ Order.succ a := by
    simpa using (Order.succ_le_succ (show (0 : Ordinal.{u}) ≤ a from bot_le))
  have hinj : Function.Injective f := by
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact (signRecursion_ne_of_lt seed p q hpq hp hq _ _ (hsucc a)
        (Order.succ_lt_succ hlt) (hgood _) (hgood _) hab).elim
    · exact heq
    · exact (signRecursion_ne_of_lt seed p q hpq hp hq _ _ (hsucc b)
        (Order.succ_lt_succ hgt) (hgood _) (hgood _) hab.symm).elim
  exact no_injection_from_ordinals _ f hinj

theorem exists_first_bad_limit (hK : IsFSpace K) (seed : UnitBall C(K, ℝ)) (p q : K)
    (hpq : ClopenInseparable p q) (hp : seed.val p = 1) (hq : seed.val q = -1) :
    ∃ d : Ordinal.{u}, IsSuccLimit d ∧ ¬ SignStageGood seed d ∧
      ∀ a, a < d → SignStageGood seed a := by
  obtain ⟨d, hd, hmin⟩ := Ordinal.lt_wf.has_min {a | ¬ SignStageGood seed a}
    (exists_bad_signStage seed p q hpq hp hq)
  have hbefore : ∀ a, a < d → SignStageGood seed a := by
    intro a had
    by_contra ha
    exact hmin a ha had
  have hd₀ : d ≠ 0 := by
    intro h
    subst d
    exact hd (signStageGood_zero seed)
  refine ⟨d, ?_, hd, hbefore⟩
  refine ⟨?_, ?_⟩
  · intro h
    exact hd₀ h.eq_bot
  · intro a hacov
    have heq : Order.succ a = d := Order.succ_eq_iff_covBy.mpr hacov
    have hs := signStageGood_succ hK seed a (hbefore a hacov.lt)
    rw [heq] at hs
    exact hd hs

end BFPP
