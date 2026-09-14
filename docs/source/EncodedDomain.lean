import BFPP.Interleaving
import BFPP.ExtensionDelay
import BFPP.TwoProfileStructure

/-! # A closed bounded convex domain in a single ordinal sequence space -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {ρ σ κ : Ordinal.{u}} [Fact (IsSuccLimit ρ)] [Fact (IsSuccLimit σ)] [Fact (IsSuccLimit κ)]

noncomputable def encodeProfiles (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) : BoundedFamily (OrdinalIndex κ) :=
  interleave (z.val.1.extend hρκ).val (z.val.2.extend hσκ).val

@[simp] theorem encodeProfiles_even (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ) :
    encodeProfiles hρκ hσκ z (evenIndex κ i) = (z.val.1.extend hρκ).val i :=
  interleave_even _ _ _

@[simp] theorem encodeProfiles_odd (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (i : OrdinalIndex κ) :
    encodeProfiles hρκ hσκ z (oddIndex κ i) = 4 + (z.val.2.extend hσκ).val i :=
  interleave_odd _ _ _

theorem encodeProfiles_isometry (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :
    Isometry (encodeProfiles hρκ hσκ) := by
  apply isometry_iff_dist_eq.mpr
  intro z w
  rw [encodeProfiles, encodeProfiles, interleave_isometry.dist_eq
    ((z.val.1.extend hρκ).val, (z.val.2.extend hσκ).val)
    ((w.val.1.extend hρκ).val, (w.val.2.extend hσκ).val)]
  change max (dist (z.val.1.extend hρκ) (w.val.1.extend hρκ))
    (dist (z.val.2.extend hσκ) (w.val.2.extend hσκ)) =
      max (dist z.val.1 w.val.1) (dist z.val.2 w.val.2)
  rw [(Profile.extend_isometry hρκ).dist_eq, (Profile.extend_isometry hσκ).dist_eq]

theorem encodeProfiles_mix (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z w : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    encodeProfiles hρκ hσκ (z.mix w r s hr hs hrs) =
      r • encodeProfiles hρκ hσκ z + s • encodeProfiles hρκ hσκ w := by
  simp only [encodeProfiles, TwoProfile.mix_first, TwoProfile.mix_second, Profile.extend_mix]
  exact interleave_affine _ _ _ _ r s hrs

def encodedSet (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) : Set (BoundedFamily (OrdinalIndex κ)) :=
  range (encodeProfiles hρκ hσκ)

theorem encodedSet_nonempty (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) : (encodedSet hρκ hσκ).Nonempty :=
  ⟨encodeProfiles hρκ hσκ TwoProfile.witness, mem_range_self _⟩

theorem encodedSet_isClosed (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) : IsClosed (encodedSet hρκ hσκ) :=
  (encodeProfiles_isometry hρκ hσκ).isUniformInducing.isComplete_range.isClosed

theorem encodedSet_convex (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) : Convex ℝ (encodedSet hρκ hσκ) := by
  intro x hx y hy r s hr hs hrs
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨z.mix w r s hr hs hrs, encodeProfiles_mix hρκ hσκ z w r s hr hs hrs⟩

theorem encodeProfiles_norm_le (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) : ‖encodeProfiles hρκ hσκ z‖ ≤ 6 := by
  letI : TopologicalSpace (OrdinalIndex κ) := ⊥
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 6)).mpr
  intro i
  rw [Real.norm_eq_abs]
  rcases index_eq_even_or_odd κ i with he | ho
  · rw [he, encodeProfiles_even, abs_of_nonneg ((z.val.1.extend hρκ).nonneg _)]
    exact ((z.val.1.extend hρκ).le_two _).trans (by norm_num)
  · rw [ho, encodeProfiles_odd]
    have hb₀ := (z.val.2.extend hσκ).nonneg (halfIndex κ i)
    have hb₁ := (z.val.2.extend hσκ).le_two (halfIndex κ i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem encodedSet_isBounded (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :
    Bornology.IsBounded (encodedSet hρκ hσκ) := by
  apply (Metric.isBounded_closedBall (x := (0 : BoundedFamily (OrdinalIndex κ))) (r := 6)).subset
  rintro x ⟨z, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using encodeProfiles_norm_le hρκ hσκ z

abbrev EncodedDomain (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :=
  {x : BoundedFamily (OrdinalIndex κ) // x ∈ encodedSet hρκ hσκ}

noncomputable def encodeIso (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :
    TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ) ≃ᵢ EncodedDomain hρκ hσκ where
  toFun z := ⟨encodeProfiles hρκ hσκ z, mem_range_self z⟩
  invFun x := x.property.choose
  left_inv z := (encodeProfiles_isometry hρκ hσκ).injective (Exists.choose_spec (mem_range_self z))
  right_inv x := Subtype.ext x.property.choose_spec
  isometry_toFun := encodeProfiles_isometry hρκ hσκ

end BFPP
