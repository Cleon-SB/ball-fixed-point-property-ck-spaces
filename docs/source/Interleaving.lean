import BFPP.OrdinalPairs

/-! # Affine isometric interleaving of two bounded channels -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {κ : Ordinal.{u}} [Fact (IsSuccLimit κ)]

noncomputable def interleaveValue (a b : BoundedFamily (OrdinalIndex κ)) (i : OrdinalIndex κ) : ℝ := by
  classical
  exact if i.val % 2 = 0 then a (halfIndex κ i) else 4 + b (halfIndex κ i)

noncomputable def interleave (a b : BoundedFamily (OrdinalIndex κ)) : BoundedFamily (OrdinalIndex κ) :=
  BoundedFamily.ofBound (interleaveValue a b) (‖a‖ + ‖b‖ + 4) (by
    intro i
    classical
    rw [Real.norm_eq_abs]
    dsimp [interleaveValue]
    split_ifs
    · have ha := a.abs_apply_le_norm (halfIndex κ i)
      linarith [norm_nonneg b]
    · calc
        |4 + b (halfIndex κ i)| ≤ |(4 : ℝ)| + |b (halfIndex κ i)| := abs_add_le _ _
        _ ≤ ‖a‖ + ‖b‖ + 4 := by
          have hb := b.abs_apply_le_norm (halfIndex κ i)
          norm_num
          linarith [norm_nonneg a])

@[simp] theorem interleave_even (a b : BoundedFamily (OrdinalIndex κ)) (i : OrdinalIndex κ) :
    interleave a b (evenIndex κ i) = a i := by
  classical
  simp [interleave, interleaveValue]

@[simp] theorem interleave_odd (a b : BoundedFamily (OrdinalIndex κ)) (i : OrdinalIndex κ) :
    interleave a b (oddIndex κ i) = 4 + b i := by
  classical
  simp [interleave, interleaveValue]

theorem interleave_isometry :
    Isometry (fun p : BoundedFamily (OrdinalIndex κ) × BoundedFamily (OrdinalIndex κ) =>
      interleave p.1 p.2) := by
  classical
  apply isometry_iff_dist_eq.mpr
  intro p q
  apply le_antisymm
  · apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).mpr
    intro i
    rcases index_eq_even_or_odd κ i with he | ho
    · rw [he, interleave_even, interleave_even]
      exact (p.1.abs_sub_apply_le_dist q.1 _).trans (le_max_left _ _)
    · rw [ho, interleave_odd, interleave_odd, add_sub_add_left_eq_sub]
      exact (p.2.abs_sub_apply_le_dist q.2 _).trans (le_max_right _ _)
  · apply max_le
    · apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).mpr
      intro i
      rw [← interleave_even p.1 p.2 i, ← interleave_even q.1 q.2 i]
      exact BoundedFamily.abs_sub_apply_le_dist _ _ _
    · apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).mpr
      intro i
      have h := BoundedFamily.abs_sub_apply_le_dist (interleave p.1 p.2) (interleave q.1 q.2)
        (oddIndex κ i)
      simpa only [interleave_odd, add_sub_add_left_eq_sub] using h

theorem interleave_affine (a b a' b' : BoundedFamily (OrdinalIndex κ))
    (r s : ℝ) (hrs : r + s = 1) :
    interleave (r • a + s • a') (r • b + s • b') =
      r • interleave a b + s • interleave a' b' := by
  classical
  letI : TopologicalSpace (OrdinalIndex κ) := ⊥
  apply BoundedContinuousFunction.ext
  intro i
  rcases index_eq_even_or_odd κ i with he | ho
  · rw [he]
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      interleave_even]
  · rw [ho]
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      interleave_odd]
    change 4 + (r * b _ + s * b' _) = r * (4 + b _) + s * (4 + b' _)
    nlinarith [hrs]

end BFPP
