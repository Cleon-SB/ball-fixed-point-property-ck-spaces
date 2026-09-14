import BFPP.SignExtension
import BFPP.Hartogs
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! # The transfinite sign-extension recursion -/

namespace BFPP

set_option autoImplicit false

open Set Order

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [NormalSpace K]

def zeroBall : UnitBall C(K, ℝ) := ⟨0, by simp⟩

def signsPositiveBefore (H : Ordinal.{u} → UnitBall C(K, ℝ)) (a : Ordinal.{u}) : Set K :=
  ⋃ b : Iio a, {t | 0 < (H b.val).val t}

def signsNegativeBefore (H : Ordinal.{u} → UnitBall C(K, ℝ)) (a : Ordinal.{u}) : Set K :=
  ⋃ b : Iio a, {t | (H b.val).val t < 0}

noncomputable def signRecursionStep (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u})
    (previous : ∀ b, b < a → UnitBall C(K, ℝ)) : UnitBall C(K, ℝ) := by
  classical
  let U : Set K := ⋃ b : Iio a, {t | 0 < (previous b.val b.property).val t}
  let V : Set K := ⋃ b : Iio a, {t | (previous b.val b.property).val t < 0}
  exact if a = 0 then zeroBall else if a = 1 then seed else
    if h : Disjoint (closure U) (closure V) then (exists_sign_extension U V h).choose else zeroBall

noncomputable def signRecursion (seed : UnitBall C(K, ℝ)) : Ordinal.{u} → UnitBall C(K, ℝ) :=
  Ordinal.lt_wf.fix (signRecursionStep seed)

theorem signRecursion_eq (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u}) :
    signRecursion seed a = signRecursionStep seed a (fun b _ => signRecursion seed b) :=
  WellFounded.fix_eq _ _ _

@[simp] theorem signRecursion_zero (seed : UnitBall C(K, ℝ)) : signRecursion seed 0 = zeroBall := by
  rw [signRecursion_eq]
  simp [signRecursionStep]

@[simp] theorem signRecursion_one (seed : UnitBall C(K, ℝ)) : signRecursion seed 1 = seed := by
  rw [signRecursion_eq]
  simp [signRecursionStep]

def SignStageGood (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u}) : Prop :=
  Disjoint (closure (signsPositiveBefore (signRecursion seed) a))
    (closure (signsNegativeBefore (signRecursion seed) a))

theorem signRecursion_extension (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u})
    (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) (ha : SignStageGood seed a) :
    (∀ t ∈ closure (signsPositiveBefore (signRecursion seed) a), (signRecursion seed a).val t = 1) ∧
    (∀ t ∈ closure (signsNegativeBefore (signRecursion seed) a), (signRecursion seed a).val t = -1) := by
  have h := (exists_sign_extension (signsPositiveBefore (signRecursion seed) a)
    (signsNegativeBefore (signRecursion seed) a) ha).choose_spec
  unfold SignStageGood signsPositiveBefore signsNegativeBefore at ha
  rw [signRecursion_eq]
  simpa only [signRecursionStep, if_neg ha₀, if_neg ha₁, dif_pos ha,
    signsPositiveBefore, signsNegativeBefore] using h

theorem signRecursion_positive_saturated (seed : UnitBall C(K, ℝ)) (a b : Ordinal.{u})
    (hab : a < b) (hb : SignStageGood seed b) (t : K)
    (ht : 0 < (signRecursion seed a).val t) : (signRecursion seed b).val t = 1 := by
  have hb₀ : b ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hab)
  by_cases hb₁ : b = 1
  · have ha₀ : a = 0 := by simpa only [hb₁, Ordinal.lt_one_iff_zero] using hab
    simp only [ha₀, signRecursion_zero, zeroBall, ContinuousMap.zero_apply] at ht
    exact (lt_irrefl _ ht).elim
  · apply (signRecursion_extension seed b hb₀ hb₁ hb).1 t
    apply subset_closure
    exact mem_iUnion.mpr ⟨⟨a, hab⟩, ht⟩

theorem signRecursion_negative_saturated (seed : UnitBall C(K, ℝ)) (a b : Ordinal.{u})
    (hab : a < b) (hb : SignStageGood seed b) (t : K)
    (ht : (signRecursion seed a).val t < 0) : (signRecursion seed b).val t = -1 := by
  have hb₀ : b ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hab)
  by_cases hb₁ : b = 1
  · have ha₀ : a = 0 := by simpa only [hb₁, Ordinal.lt_one_iff_zero] using hab
    simp only [ha₀, signRecursion_zero, zeroBall, ContinuousMap.zero_apply] at ht
    exact (lt_irrefl _ ht).elim
  · apply (signRecursion_extension seed b hb₀ hb₁ hb).2 t
    apply subset_closure
    exact mem_iUnion.mpr ⟨⟨a, hab⟩, ht⟩

@[simp] theorem signStageGood_zero (seed : UnitBall C(K, ℝ)) : SignStageGood seed 0 := by
  simp [SignStageGood, signsPositiveBefore, signsNegativeBefore]

theorem signsPositiveBefore_succ (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u})
    (ha : SignStageGood seed a) :
    signsPositiveBefore (signRecursion seed) (Order.succ a) =
      {t | 0 < (signRecursion seed a).val t} := by
  ext t
  simp only [signsPositiveBefore, mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb⟩
    have hba : b.val ≤ a := Order.lt_succ_iff.mp b.property
    rcases hba.eq_or_lt with heq | hlt
    · simpa only [heq] using hb
    · rw [signRecursion_positive_saturated seed b.val a hlt ha t hb]
      norm_num
  · intro ht
    exact ⟨⟨a, Order.lt_succ a⟩, ht⟩

theorem signsNegativeBefore_succ (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u})
    (ha : SignStageGood seed a) :
    signsNegativeBefore (signRecursion seed) (Order.succ a) =
      {t | (signRecursion seed a).val t < 0} := by
  ext t
  simp only [signsNegativeBefore, mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb⟩
    have hba : b.val ≤ a := Order.lt_succ_iff.mp b.property
    rcases hba.eq_or_lt with heq | hlt
    · simpa only [heq] using hb
    · rw [signRecursion_negative_saturated seed b.val a hlt ha t hb]
      norm_num
  · intro ht
    exact ⟨⟨a, Order.lt_succ a⟩, ht⟩

theorem signStageGood_succ (hK : IsFSpace K) (seed : UnitBall C(K, ℝ)) (a : Ordinal.{u})
    (ha : SignStageGood seed a) : SignStageGood seed (Order.succ a) := by
  unfold SignStageGood
  rw [signsPositiveBefore_succ seed a ha, signsNegativeBefore_succ seed a ha]
  exact hK.disjoint_sign_closures _

theorem signRecursion_at_points (seed : UnitBall C(K, ℝ)) (p q : K)
    (hp : seed.val p = 1) (hq : seed.val q = -1) (a : Ordinal.{u})
    (ha₁ : 1 ≤ a) (ha : SignStageGood seed a) :
    (signRecursion seed a).val p = 1 ∧ (signRecursion seed a).val q = -1 := by
  rcases ha₁.eq_or_lt with heq | hlt
  · simpa only [← heq, signRecursion_one] using And.intro hp hq
  · constructor
    · apply signRecursion_positive_saturated seed 1 a hlt ha p
      simp only [signRecursion_one, hp]
      norm_num
    · apply signRecursion_negative_saturated seed 1 a hlt ha q
      simp only [signRecursion_one, hq]
      norm_num

end BFPP
