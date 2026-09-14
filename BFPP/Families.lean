import BFPP.Analysis
import BFPP.CenteredSynthesis

/-! # Increasing families and their level sets -/

namespace BFPP

set_option autoImplicit false

open Set

universe u v w

structure IncreasingFamily (K : Type u) (ι : Type v)
    [TopologicalSpace K] [LinearOrder ι] [OrderBot ι] where
  functions : ι → C(K, ℝ)
  monotone : ∀ t, Monotone (fun i => functions i t)
  bounds : ∀ i t, 0 ≤ functions i t ∧ functions i t ≤ 1
  at_bot : functions ⊥ = 0

namespace IncreasingFamily

variable {K : Type u} {ι : Type v} [TopologicalSpace K] [LinearOrder ι] [OrderBot ι]

def levels (F : IncreasingFamily K ι) (i : ι) : Set K := {t | F.functions i t = 1}

theorem levels_monotone (F : IncreasingFamily K ι) : Monotone F.levels := by
  intro i j hij t ht
  have hm := F.monotone t hij
  have hb := (F.bounds j t).2
  change F.functions i t = 1 at ht
  change F.functions j t = 1
  linarith

@[simp] theorem levels_bot (F : IncreasingFamily K ι) : F.levels ⊥ = ∅ := by
  ext t
  simp [levels, F.at_bot]

end IncreasingFamily

structure InseparablePair (K : Type u) (ι : Type v) (κ : Type w)
    [TopologicalSpace K] [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ] where
  positive : IncreasingFamily K ι
  negative : IncreasingFamily K κ
  orthogonal : ∀ i j t, positive.functions i t * negative.functions j t = 0
  inseparable : (closure (⋃ i, positive.levels i) ∩ closure (⋃ j, negative.levels j)).Nonempty

namespace InseparablePair

variable {K : Type u} {ι : Type v} {κ : Type w}
  [TopologicalSpace K] [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

def levels (F : InseparablePair K ι κ) : InseparableLevels K ι κ where
  positive := F.positive.levels
  negative := F.negative.levels
  positive_mono := F.positive.levels_monotone
  negative_mono := F.negative.levels_monotone
  positive_bot := F.positive.levels_bot
  negative_bot := F.negative.levels_bot
  inseparable := F.inseparable

theorem disjoint_channels (F : InseparablePair K ι κ) (t : K) :
    (∀ i, F.positive.functions i t = 0) ∨ (∀ j, F.negative.functions j t = 0) := by
  classical
  by_cases h : ∀ i, F.positive.functions i t = 0
  · exact Or.inl h
  · right
    obtain ⟨i, hi⟩ := not_forall.mp h
    intro j
    exact (mul_eq_zero.mp (F.orthogonal i j t)).resolve_left hi

theorem negative_zero_at_positive_level (F : InseparablePair K ι κ) (i : ι) (t : K)
    (ht : t ∈ F.positive.levels i) : ∀ j, F.negative.functions j t = 0 := by
  intro j
  have h := F.orthogonal i j t
  change F.positive.functions i t = 1 at ht
  simpa only [ht, one_mul] using h

theorem positive_zero_at_negative_level (F : InseparablePair K ι κ) (j : κ) (t : K)
    (ht : t ∈ F.negative.levels j) : ∀ i, F.positive.functions i t = 0 := by
  intro i
  have h := F.orthogonal i j t
  change F.negative.functions j t = 1 at ht
  simpa only [ht, mul_one] using h

end InseparablePair
end BFPP
