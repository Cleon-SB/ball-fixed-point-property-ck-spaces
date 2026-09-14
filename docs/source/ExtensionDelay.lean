import BFPP.ProfileExtension

/-! # Delay commutes with constant-tail extension -/

namespace BFPP.Profile

set_option autoImplicit false
open Set Order

universe u v

theorem le_delayValue_of_lt {ι : Type v} [LinearOrder ι] [OrderBot ι]
    (a : Profile ι) (j i : ι) (hji : j < i) : a.val j ≤ a.delayValue i := by
  classical
  have hi : i ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hji)
  rw [delayValue, if_neg hi]
  exact le_ciSup (a.prefix_bddAbove i) ⟨j, hji⟩

theorem delayValue_le_of_forall_lt {ι : Type v} [LinearOrder ι] [OrderBot ι]
    (a : Profile ι) (i : ι) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j, j < i → a.val j ≤ c) : a.delayValue i ≤ c := by
  classical
  by_cases hi : i = ⊥
  · simpa only [hi, delayValue_bot] using hc
  · letI : Nonempty (Iio i) := ⟨⟨⊥, lt_of_le_of_ne bot_le (Ne.symm hi)⟩⟩
    rw [delayValue, if_neg hi]
    exact ciSup_le (fun j => h j.val j.property)

variable {ρ κ : Ordinal.{u}} [Fact (IsSuccLimit ρ)] [Fact (IsSuccLimit κ)]

theorem extend_delay (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) :
    (a.extend hρκ).delay = a.delay.extend hρκ := by
  classical
  letI : TopologicalSpace (OrdinalIndex κ) := ⊥
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro i
  rw [delay_apply]
  by_cases hi : i.val < ρ
  · rw [a.delay.extend_apply_lt hρκ i hi, delay_apply]
    apply le_antisymm
    · apply (a.extend hρκ).delayValue_le_of_forall_lt i _ (a.delayValue_nonneg ⟨i.val, hi⟩)
      intro j hji
      have hjρ : j.val < ρ := lt_trans hji hi
      rw [a.extend_apply_lt hρκ j hjρ]
      exact a.le_delayValue_of_lt ⟨j.val, hjρ⟩ ⟨i.val, hi⟩ hji
    · apply a.delayValue_le_of_forall_lt ⟨i.val, hi⟩ _ ((a.extend hρκ).delayValue_nonneg i)
      intro j hji
      let j' : OrdinalIndex κ := ⟨j.val, lt_of_lt_of_le j.property hρκ⟩
      have h := (a.extend hρκ).le_delayValue_of_lt j' i hji
      rwa [a.extend_at_source hρκ j] at h
  · have hge : ρ ≤ i.val := le_of_not_gt hi
    rw [a.delay.extend_apply_ge hρκ i hge, tail_delay]
    apply le_antisymm
    · exact (a.extend hρκ).delayValue_le_of_forall_lt i _ a.tail_nonneg
        (fun j _ => a.extendValue_le_tail j)
    · apply ciSup_le
      intro j
      let j' : OrdinalIndex κ := ⟨j.val, lt_of_lt_of_le j.property hρκ⟩
      have hji : j' < i := show j.val < i.val from lt_of_lt_of_le j.property hge
      have h := (a.extend hρκ).le_delayValue_of_lt j' i hji
      rwa [a.extend_at_source hρκ j] at h

end BFPP.Profile
