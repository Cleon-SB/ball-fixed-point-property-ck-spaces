import BFPP.TwoProfileGeometry

/-! # Completeness and convex combinations of the two-profile domain -/

namespace BFPP.TwoProfile

set_option autoImplicit false

universe u v
variable {ι : Type u} {κ : Type v}
  [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

instance : CompleteSpace (TwoProfile ι κ) := by
  letI : CompleteSpace {z // z ∈ twoProfileSet ι κ} := twoProfileSet_isClosed.completeSpace_coe
  let e : TwoProfile ι κ ≃ᵢ {z // z ∈ twoProfileSet ι κ} :=
    ⟨ambientEquiv, ambientEquiv_isometry⟩
  exact e.completeSpace_iff.mpr inferInstance

noncomputable def mix (z w : TwoProfile ι κ) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) : TwoProfile ι κ := by
  refine ⟨(z.val.1.mix w.val.1 r s hr hs hrs, z.val.2.mix w.val.2 r s hr hs hrs), ?_⟩
  rw [Profile.tail_mix, Profile.tail_mix]
  have h₁ := mul_le_mul_of_nonneg_left z.property hr
  have h₂ := mul_le_mul_of_nonneg_left w.property hs
  nlinarith

@[simp] theorem mix_first (z w : TwoProfile ι κ) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    (z.mix w r s hr hs hrs).val.1 = z.val.1.mix w.val.1 r s hr hs hrs := rfl

@[simp] theorem mix_second (z w : TwoProfile ι κ) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    (z.mix w r s hr hs hrs).val.2 = z.val.2.mix w.val.2 r s hr hs hrs := rfl

end BFPP.TwoProfile
