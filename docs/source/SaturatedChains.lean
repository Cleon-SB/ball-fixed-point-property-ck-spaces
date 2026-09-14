import BFPP.Families

/-! # Inseparable families obtained from saturated sign chains -/

namespace BFPP

set_option autoImplicit false

open Set

universe u v
variable {K : Type u} {ι : Type v} [TopologicalSpace K] [CompactSpace K]
  [LinearOrder ι] [OrderBot ι]

structure SaturatedSignChain (K : Type u) (ι : Type v)
    [TopologicalSpace K] [CompactSpace K] [LinearOrder ι] [OrderBot ι] where
  functions : ι → UnitBall C(K, ℝ)
  at_bot : (functions ⊥).val = 0
  positive : ∀ i j, i < j → ∀ t, 0 < (functions i).val t → (functions j).val t = 1
  negative : ∀ i j, i < j → ∀ t, (functions i).val t < 0 → (functions j).val t = -1
  terminal : (closure (⋃ i, {t | 0 < (functions i).val t}) ∩
    closure (⋃ i, {t | (functions i).val t < 0})).Nonempty

namespace SaturatedSignChain

noncomputable def positivePart (H : SaturatedSignChain K ι) (i : ι) : C(K, ℝ) :=
  ⟨fun t => max ((H.functions i).val t) 0, (H.functions i).val.continuous.max continuous_const⟩

noncomputable def negativePart (H : SaturatedSignChain K ι) (i : ι) : C(K, ℝ) :=
  ⟨fun t => max (-(H.functions i).val t) 0, (H.functions i).val.continuous.neg.max continuous_const⟩

noncomputable def positiveFamily (H : SaturatedSignChain K ι) : IncreasingFamily K ι where
  functions := H.positivePart
  monotone t := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    change max ((H.functions i).val t) 0 ≤ max ((H.functions j).val t) 0
    by_cases hi : 0 < (H.functions i).val t
    · rw [H.positive i j hij t hi, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
      exact max_le (continuousBall_bounds (H.functions i) t).2 (by norm_num)
    · rw [max_eq_right (le_of_not_gt hi)]
      exact le_max_right _ _
  bounds i t := ⟨le_max_right _ _,
    max_le (continuousBall_bounds (H.functions i) t).2 (by norm_num)⟩
  at_bot := by
    ext t
    change max ((H.functions ⊥).val t) 0 = 0
    simp [H.at_bot]

noncomputable def negativeFamily (H : SaturatedSignChain K ι) : IncreasingFamily K ι where
  functions := H.negativePart
  monotone t := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    change max (-(H.functions i).val t) 0 ≤ max (-(H.functions j).val t) 0
    by_cases hi : (H.functions i).val t < 0
    · rw [H.negative i j hij t hi, neg_neg, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
      have h := (continuousBall_bounds (H.functions i) t).1
      exact max_le (by linarith) (by norm_num)
    · rw [max_eq_right (neg_nonpos.mpr (le_of_not_gt hi))]
      exact le_max_right _ _
  bounds i t := by
    refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
    have h := (continuousBall_bounds (H.functions i) t).1
    linarith
  at_bot := by
    ext t
    change max (-(H.functions ⊥).val t) 0 = 0
    simp [H.at_bot]

theorem orthogonal_parts (H : SaturatedSignChain K ι) (i j : ι) (t : K) :
    H.positiveFamily.functions i t * H.negativeFamily.functions j t = 0 := by
  change max ((H.functions i).val t) 0 * max (-(H.functions j).val t) 0 = 0
  by_cases hi : 0 < (H.functions i).val t
  · by_cases hj : (H.functions j).val t < 0
    · exfalso
      rcases lt_trichotomy i j with hij | rfl | hji
      · have h := H.positive i j hij t hi
        linarith
      · linarith
      · have h := H.negative j i hji t hj
        linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_not_gt hj)), mul_zero]
  · rw [max_eq_right (le_of_not_gt hi), zero_mul]

theorem positive_union [NoMaxOrder ι] (H : SaturatedSignChain K ι) :
    (⋃ i, H.positiveFamily.levels i) = ⋃ i, {t | 0 < (H.functions i).val t} := by
  ext t
  simp only [mem_iUnion, IncreasingFamily.levels, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change max ((H.functions i).val t) 0 = 1 at hi
    by_contra h
    rw [max_eq_right (le_of_not_gt h)] at hi
    norm_num at hi
  · rintro ⟨i, hi⟩
    obtain ⟨j, hij⟩ := exists_gt i
    refine ⟨j, ?_⟩
    change max ((H.functions j).val t) 0 = 1
    rw [H.positive i j hij t hi]
    norm_num

theorem negative_union [NoMaxOrder ι] (H : SaturatedSignChain K ι) :
    (⋃ i, H.negativeFamily.levels i) = ⋃ i, {t | (H.functions i).val t < 0} := by
  ext t
  simp only [mem_iUnion, IncreasingFamily.levels, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change max (-(H.functions i).val t) 0 = 1 at hi
    by_contra h
    rw [max_eq_right (neg_nonpos.mpr (le_of_not_gt h))] at hi
    norm_num at hi
  · rintro ⟨i, hi⟩
    obtain ⟨j, hij⟩ := exists_gt i
    refine ⟨j, ?_⟩
    change max (-(H.functions j).val t) 0 = 1
    rw [H.negative i j hij t hi]
    norm_num

noncomputable def toInseparablePair [NoMaxOrder ι] (H : SaturatedSignChain K ι) :
    InseparablePair K ι ι where
  positive := H.positiveFamily
  negative := H.negativeFamily
  orthogonal := H.orthogonal_parts
  inseparable := by
    rw [H.positive_union, H.negative_union]
    exact H.terminal

end SaturatedSignChain
end BFPP
