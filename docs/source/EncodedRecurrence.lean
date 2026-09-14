import BFPP.EncodedMaps
import BFPP.TransfinitePropagator
import BFPP.DelayPrefixBound

/-! # The encoded delay is a transfinite contractive propagator -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {ρ σ κ : Ordinal.{u}} [Fact (IsSuccLimit ρ)] [Fact (IsSuccLimit σ)]
    [hκ : Fact (IsSuccLimit κ)]

theorem encodeProfiles_delay_interleave (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) :
    encodeProfiles hρκ hσκ z.delay =
      interleave (z.val.1.extend hρκ).delay.val (z.val.2.extend hσκ).delay.val := by
  change interleave (z.val.1.delay.extend hρκ).val (z.val.2.delay.extend hσκ).val = _
  rw [← Profile.extend_delay, ← Profile.extend_delay]

theorem encodeProfiles_delay_causal (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z w : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ) :
    dist (encodeProfiles hρκ hσκ z.delay i) (encodeProfiles hρκ hσκ w.delay i) ≤
      dist (restrictFamily i.property.le (encodeProfiles hρκ hσκ z))
        (restrictFamily i.property.le (encodeProfiles hρκ hσκ w)) := by
  classical
  let c := dist (restrictFamily i.property.le (encodeProfiles hρκ hσκ z))
    (restrictFamily i.property.le (encodeProfiles hρκ hσκ w))
  change |encodeProfiles hρκ hσκ z.delay i - encodeProfiles hρκ hσκ w.delay i| ≤ c
  rw [encodeProfiles_delay_interleave, encodeProfiles_delay_interleave]
  rcases index_eq_even_or_odd κ i with he | ho
  · have hi : i.val % 2 = 0 := by rw [he]; exact evenIndex_mod _ _
    simp only [interleave, BoundedFamily.ofBound_apply, interleaveValue, if_pos hi,
      Profile.delay_apply]
    apply Profile.delayValue_abs_sub_le_of_prefix _ _ _ c dist_nonneg
    intro j hj
    have hj' : evenIndex κ j < i := by rw [he]; exact evenIndex_strictMono κ hj
    have hh := BoundedFamily.abs_sub_apply_le_dist
      (restrictFamily i.property.le (encodeProfiles hρκ hσκ z))
      (restrictFamily i.property.le (encodeProfiles hρκ hσκ w))
      ⟨(evenIndex κ j).val, hj'⟩
    change |encodeProfiles hρκ hσκ z (evenIndex κ j) -
      encodeProfiles hρκ hσκ w (evenIndex κ j)| ≤ c at hh
    rw [encodeProfiles_even, encodeProfiles_even] at hh
    exact hh
  · have hi₁ : i.val % 2 = 1 := by rw [ho]; exact oddIndex_mod _ _
    have hi : i.val % 2 ≠ 0 := by rw [hi₁]; norm_num
    simp only [interleave, BoundedFamily.ofBound_apply, interleaveValue, if_neg hi,
      add_sub_add_left_eq_sub, Profile.delay_apply]
    apply Profile.delayValue_abs_sub_le_of_prefix _ _ _ c dist_nonneg
    intro j hj
    have hj' : oddIndex κ j < i := by rw [ho]; exact oddIndex_strictMono κ hj
    have hh := BoundedFamily.abs_sub_apply_le_dist
      (restrictFamily i.property.le (encodeProfiles hρκ hσκ z))
      (restrictFamily i.property.le (encodeProfiles hρκ hσκ w))
      ⟨(oddIndex κ j).val, hj'⟩
    change |encodeProfiles hρκ hσκ z (oddIndex κ j) -
      encodeProfiles hρκ hσκ w (oddIndex κ j)| ≤ c at hh
    rw [encodeProfiles_odd, encodeProfiles_odd, add_sub_add_left_eq_sub] at hh
    exact hh

theorem encodeProfiles_delay_limit (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ)
    (hi : IsSuccLimit i.val) :
    encodeProfiles hρκ hσκ z.delay i =
      lowerEnvelope (restrictFamily i.property.le (encodeProfiles hρκ hσκ z)) := by
  letI : Fact (IsSuccLimit i.val) := ⟨hi⟩
  have he : evenIndex κ i = i := Subtype.ext (ordinal_two_mul_limit i.val hi)
  have hprefix := interleave_lowerEnvelope_prefix i.property
    (z.val.1.extend hρκ) (z.val.2.extend hσκ)
  calc
    encodeProfiles hρκ hσκ z.delay i =
        encodeProfiles hρκ hσκ z.delay (evenIndex κ i) :=
      congrArg (encodeProfiles hρκ hσκ z.delay) he.symm
    _ = (z.val.1.delay.extend hρκ).val i := encodeProfiles_even hρκ hσκ z.delay i
    _ = (z.val.1.extend hρκ).delay.val i := by rw [← Profile.extend_delay]
    _ = lowerEnvelope (restrictFamily i.property.le (encodeProfiles hρκ hσκ z)) := hprefix.symm

theorem encodedPropagator_isTCP (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :
    IsTCP (encodedSet hρκ hσκ) (encodedPropagator hρκ hσκ) := by
  apply isTCP_of_causal (encodedPropagator hρκ hσκ) hκ.out.pos
    (encodedSet_nonempty hρκ hσκ) 0
  · intro x
    obtain ⟨z, rfl⟩ := (encodeIso hρκ hσκ).surjective x
    rw [encodedPropagator_encode]
    change encodeProfiles hρκ hσκ z.delay ⊥ = 0
    have h := encodeProfiles_even hρκ hσκ z.delay ⊥
    simpa only [evenIndex_bot, Profile.at_bot] using h
  · intro i x y
    obtain ⟨z, rfl⟩ := (encodeIso hρκ hσκ).surjective x
    obtain ⟨w, rfl⟩ := (encodeIso hρκ hσκ).surjective y
    rw [encodedPropagator_encode, encodedPropagator_encode]
    exact encodeProfiles_delay_causal hρκ hσκ z w i
  · intro i hi x
    obtain ⟨z, rfl⟩ := (encodeIso hρκ hσκ).surjective x
    rw [encodedPropagator_encode]
    exact encodeProfiles_delay_limit hρκ hσκ z i hi

end BFPP
