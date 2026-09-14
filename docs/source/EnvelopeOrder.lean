import BFPP.Envelopes

/-! # Order estimates for tail envelopes -/

namespace BFPP

set_option autoImplicit false
open Set

variable {ι : Type*} [Preorder ι]

theorem lowerTail_le_point (f : BoundedFamily ι) (b j : ι) (hj : b ≤ j) :
    lowerTail f b ≤ f j :=
  ciInf_le (BoundedFamily.bddBelow_range (BoundedFamily.reindex (fun k : Ici b => k.val) f)) ⟨j, hj⟩

theorem point_le_upperTail (f : BoundedFamily ι) (b j : ι) (hj : b ≤ j) :
    f j ≤ upperTail f b :=
  le_ciSup (BoundedFamily.bddAbove_range (BoundedFamily.reindex (fun k : Ici b => k.val) f)) ⟨j, hj⟩

theorem le_lowerTail (f : BoundedFamily ι) (b : ι) (c : ℝ)
    (h : ∀ j, b ≤ j → c ≤ f j) : c ≤ lowerTail f b := by
  letI : Nonempty (Ici b) := ⟨⟨b, le_rfl⟩⟩
  exact le_ciInf (fun j => h j.val j.property)

theorem upperTail_le (f : BoundedFamily ι) (b : ι) (c : ℝ)
    (h : ∀ j, b ≤ j → f j ≤ c) : upperTail f b ≤ c := by
  letI : Nonempty (Ici b) := ⟨⟨b, le_rfl⟩⟩
  exact ciSup_le (fun j => h j.val j.property)

theorem lowerTail_le_lowerEnvelope (f : BoundedFamily ι) (b : ι) :
    lowerTail f b ≤ lowerEnvelope f := le_ciSup (lowerTails f).bddAbove_range b

theorem upperEnvelope_le_upperTail (f : BoundedFamily ι) (b : ι) :
    upperEnvelope f ≤ upperTail f b := ciInf_le (upperTails f).bddBelow_range b

theorem lowerEnvelope_le [Nonempty ι] (f : BoundedFamily ι) (c : ℝ)
    (h : ∀ b, lowerTail f b ≤ c) : lowerEnvelope f ≤ c := ciSup_le h

theorem le_upperEnvelope [Nonempty ι] (f : BoundedFamily ι) (c : ℝ)
    (h : ∀ b, c ≤ upperTail f b) : c ≤ upperEnvelope f := le_ciInf h

end BFPP
