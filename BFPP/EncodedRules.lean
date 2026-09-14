import BFPP.EncodedRecurrence

/-! # Explicit formulas for the encoded successor and limit coordinates -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {ρ σ κ : Ordinal.{u}} [Fact (IsSuccLimit ρ)] [Fact (IsSuccLimit σ)]
    [hκ : Fact (IsSuccLimit κ)]

theorem encodeProfiles_delay_even_succ (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ) :
    encodeProfiles hρκ hσκ z.delay (evenIndex κ (succ i)) =
      encodeProfiles hρκ hσκ z (evenIndex κ i) := by
  rw [encodeProfiles_delay_interleave, interleave_even, Profile.delay_apply,
    Profile.delayValue_succ, encodeProfiles_even]

theorem encodeProfiles_delay_odd_succ (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ) :
    encodeProfiles hρκ hσκ z.delay (oddIndex κ (succ i)) =
      encodeProfiles hρκ hσκ z (oddIndex κ i) := by
  rw [encodeProfiles_delay_interleave, interleave_odd, Profile.delay_apply,
    Profile.delayValue_succ, encodeProfiles_odd]

theorem encodeProfiles_delay_odd_zero (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) :
    encodeProfiles hρκ hσκ z.delay (oddIndex κ ⊥) = 4 := by
  rw [encodeProfiles_odd, Profile.at_bot, add_zero]

theorem encodeProfiles_delay_upper_limit (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ)
    (hi : IsSuccLimit i.val) :
    encodeProfiles hρκ hσκ z.delay (oddIndex κ i) =
      upperEnvelope (restrictFamily i.property.le (encodeProfiles hρκ hσκ z)) := by
  letI : Fact (IsSuccLimit i.val) := ⟨hi⟩
  rw [encodeProfiles_delay_interleave, interleave_odd, Profile.delay_apply]
  exact (interleave_upperEnvelope_prefix i.property
    (z.val.1.extend hρκ) (z.val.2.extend hσκ)).symm

/-- At a limit ordinal the odd encoded coordinate is its immediate successor. -/
theorem oddIndex_limit_val (i : OrdinalIndex κ) (hi : IsSuccLimit i.val) :
    (oddIndex κ i).val = i.val + 1 := by
  change 2 * i.val + 1 = i.val + 1
  rw [ordinal_two_mul_limit i.val hi]

end BFPP
