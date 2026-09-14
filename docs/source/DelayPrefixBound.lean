import BFPP.Profiles

/-! # The delay estimate only needs strict predecessors -/

namespace BFPP.Profile

set_option autoImplicit false
open Set

variable {ι : Type*} [LinearOrder ι] [OrderBot ι]

theorem delayValue_abs_sub_le_of_prefix (a b : Profile ι) (i : ι) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j, j < i → |a.val j - b.val j| ≤ c) : |a.delayValue i - b.delayValue i| ≤ c := by
  classical
  by_cases hi : i = ⊥
  · simpa only [hi, delayValue_bot, sub_self, abs_zero] using hc
  · letI : Nonempty (Iio i) := ⟨⟨⊥, lt_of_le_of_ne bot_le (Ne.symm hi)⟩⟩
    rw [delayValue, if_neg hi, delayValue, if_neg hi]
    exact abs_ciSup_sub_ciSup_le _ _ (a.prefix_bddAbove i) (b.prefix_bddAbove i) c
      (fun j => h j.val j.property)

end BFPP.Profile
