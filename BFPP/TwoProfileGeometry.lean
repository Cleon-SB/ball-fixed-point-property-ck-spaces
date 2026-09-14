import BFPP.TwoProfiles
import BFPP.ProfileGeometry
import Mathlib.Analysis.Normed.Module.Convex

/-! # The coefficient domain as a closed bounded convex subset of a Banach space -/

namespace BFPP

set_option autoImplicit false

open Set

universe u v
variable {ι : Type u} {κ : Type v}
  [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

def twoProfileSet (ι : Type u) (κ : Type v)
    [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ] :
    Set (BoundedFamily ι × BoundedFamily κ) :=
  {z | z.1 ∈ profileSet ι ∧ z.2 ∈ profileSet κ ∧
    2 ≤ BoundedFamily.supremum z.1 + BoundedFamily.supremum z.2}

theorem twoProfileSet_isClosed : IsClosed (twoProfileSet ι κ) := by
  have h₁ : IsClosed {z : BoundedFamily ι × BoundedFamily κ | z.1 ∈ profileSet ι} :=
    (profileSet_isClosed (ι := ι)).preimage continuous_fst
  have h₂ : IsClosed {z : BoundedFamily ι × BoundedFamily κ | z.2 ∈ profileSet κ} :=
    (profileSet_isClosed (ι := κ)).preimage continuous_snd
  have h₃ : IsClosed {z : BoundedFamily ι × BoundedFamily κ |
      2 ≤ BoundedFamily.supremum z.1 + BoundedFamily.supremum z.2} :=
    isClosed_le continuous_const
      ((BoundedFamily.supremum_nonexpansive.continuous.comp continuous_fst).add
        (BoundedFamily.supremum_nonexpansive.continuous.comp continuous_snd))
  exact h₁.inter (h₂.inter h₃)

theorem twoProfileSet_convex : Convex ℝ (twoProfileSet ι κ) := by
  intro x hx y hy r s hr hs hrs
  refine ⟨profileSet_convex hx.1 hy.1 hr hs hrs,
    profileSet_convex hx.2.1 hy.2.1 hr hs hrs, ?_⟩
  let a : Profile ι := ⟨x.1, hx.1⟩
  let a' : Profile ι := ⟨y.1, hy.1⟩
  let b : Profile κ := ⟨x.2, hx.2.1⟩
  let b' : Profile κ := ⟨y.2, hy.2.1⟩
  change 2 ≤ (a.mix a' r s hr hs hrs).tail + (b.mix b' r s hr hs hrs).tail
  rw [Profile.tail_mix, Profile.tail_mix]
  have hx' : 2 ≤ a.tail + b.tail := hx.2.2
  have hy' : 2 ≤ a'.tail + b'.tail := hy.2.2
  have h₁ := mul_le_mul_of_nonneg_left hx' hr
  have h₂ := mul_le_mul_of_nonneg_left hy' hs
  nlinarith

theorem twoProfileSet_norm_le (z : BoundedFamily ι × BoundedFamily κ)
    (hz : z ∈ twoProfileSet ι κ) : ‖z‖ ≤ 2 := by
  change max ‖z.1‖ ‖z.2‖ ≤ 2
  exact max_le (Profile.norm_le_two ⟨z.1, hz.1⟩)
    (Profile.norm_le_two ⟨z.2, hz.2.1⟩)

theorem twoProfileSet_isBounded : Bornology.IsBounded (twoProfileSet ι κ) := by
  apply (Metric.isBounded_closedBall (x := (0 : BoundedFamily ι × BoundedFamily κ)) (r := 2)).subset
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using twoProfileSet_norm_le z hz

noncomputable def TwoProfile.witness [NoMaxOrder ι] [NoMaxOrder κ] : TwoProfile ι κ :=
  ⟨(Profile.stepOne, Profile.stepOne), by simp only [Profile.tail_stepOne]; norm_num⟩

theorem twoProfileSet_nonempty [NoMaxOrder ι] [NoMaxOrder κ] :
    (twoProfileSet ι κ).Nonempty := by
  let z : TwoProfile ι κ := TwoProfile.witness
  exact ⟨(z.val.1.val, z.val.2.val), z.val.1.property, z.val.2.property, z.property⟩

/-- The two presentations of the domain have exactly the same metric. -/
def TwoProfile.ambientEquiv : TwoProfile ι κ ≃ {z // z ∈ twoProfileSet ι κ} where
  toFun z := ⟨(z.val.1.val, z.val.2.val), z.val.1.property, z.val.2.property, z.property⟩
  invFun z := ⟨(⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2.1⟩), z.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem TwoProfile.ambientEquiv_isometry :
    Isometry (TwoProfile.ambientEquiv : TwoProfile ι κ → {z // z ∈ twoProfileSet ι κ}) :=
  fun _ _ => rfl

end BFPP
