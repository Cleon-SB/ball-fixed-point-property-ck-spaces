import BFPP.OrdinalIndex
import BFPP.ProfileGeometry

/-! # Constant-tail extension of ordinal profiles -/

namespace BFPP.Profile

set_option autoImplicit false
open Set Order

universe u
variable {ρ κ : Ordinal.{u}} [hρ : Fact (IsSuccLimit ρ)] [hκ : Fact (IsSuccLimit κ)]

noncomputable def extendValue (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex κ) : ℝ := by
  classical
  exact if hi : i.val < ρ then a.val ⟨i.val, hi⟩ else a.tail

theorem extendValue_bounds (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex κ) :
    0 ≤ a.extendValue i ∧ a.extendValue i ≤ 2 := by
  classical
  dsimp [extendValue]
  split_ifs with hi
  · exact ⟨a.nonneg _, a.le_two _⟩
  · exact ⟨a.tail_nonneg, a.tail_le_two⟩

theorem extendValue_le_tail (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex κ) :
    a.extendValue i ≤ a.tail := by
  classical
  dsimp [extendValue]
  split_ifs with hi
  · exact a.le_tail _
  · exact le_rfl

theorem extendValue_monotone (a : Profile (OrdinalIndex ρ)) :
    Monotone (a.extendValue : OrdinalIndex κ → ℝ) := by
  classical
  intro i j hij
  dsimp [extendValue]
  by_cases hi : i.val < ρ
  · by_cases hj : j.val < ρ
    · simp only [dif_pos hi, dif_pos hj]
      exact a.monotone hij
    · simp only [dif_pos hi, dif_neg hj]
      exact a.le_tail _
  · have hj : ¬ j.val < ρ := fun hj => hi (lt_of_le_of_lt hij hj)
    simp only [dif_neg hi, dif_neg hj]
    exact le_rfl

noncomputable def extend (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) :
    Profile (OrdinalIndex κ) := by
  let f : BoundedFamily (OrdinalIndex κ) := BoundedFamily.ofBound a.extendValue 2
    (fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (a.extendValue_bounds i).1]
                 exact (a.extendValue_bounds i).2)
  refine ⟨f, ?_, a.extendValue_monotone, fun i => a.extendValue_bounds i⟩
  classical
  change (if hi : (0 : Ordinal.{u}) < ρ then a.val ⟨0, hi⟩ else a.tail) = 0
  rw [dif_pos hρ.out.pos]
  exact a.at_bot

@[simp] theorem extend_apply (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex κ) :
    (a.extend hρκ).val i = a.extendValue i := rfl

theorem extend_apply_lt (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex κ)
    (hi : i.val < ρ) : (a.extend hρκ).val i = a.val ⟨i.val, hi⟩ := by
  classical
  simp only [extend_apply, extendValue, dif_pos hi]

theorem extend_apply_ge (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex κ)
    (hi : ρ ≤ i.val) : (a.extend hρκ).val i = a.tail := by
  classical
  simp only [extend_apply, extendValue, dif_neg (not_lt_of_ge hi)]

theorem extend_at_source (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) (i : OrdinalIndex ρ) :
    (a.extend hρκ).val ⟨i.val, lt_of_lt_of_le i.property hρκ⟩ = a.val i :=
  a.extend_apply_lt hρκ _ i.property

@[simp] theorem tail_extend (hρκ : ρ ≤ κ) (a : Profile (OrdinalIndex ρ)) :
    (a.extend hρκ).tail = a.tail := by
  apply le_antisymm
  · exact ciSup_le a.extendValue_le_tail
  · apply ciSup_le
    intro i
    rw [← a.extend_at_source hρκ i]
    exact (a.extend hρκ).le_tail _

theorem extend_nonexpansive (hρκ : ρ ≤ κ) :
    LipschitzWith 1 (extend hρκ : Profile (OrdinalIndex ρ) → Profile (OrdinalIndex κ)) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  change dist (a.extend hρκ).val (b.extend hρκ).val ≤ dist a b
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).mpr
  intro i
  by_cases hi : i.val < ρ
  · rw [a.extend_apply_lt hρκ i hi, b.extend_apply_lt hρκ i hi]
    exact BoundedFamily.abs_sub_apply_le_dist a.val b.val _
  · rw [a.extend_apply_ge hρκ i (le_of_not_gt hi), b.extend_apply_ge hρκ i (le_of_not_gt hi)]
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using tail_nonexpansive.dist_le_mul a b

theorem extend_isometry (hρκ : ρ ≤ κ) :
    Isometry (extend hρκ : Profile (OrdinalIndex ρ) → Profile (OrdinalIndex κ)) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using (extend_nonexpansive hρκ).dist_le_mul a b
  · change dist a.val b.val ≤ dist (a.extend hρκ) (b.extend hρκ)
    apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).mpr
    intro i
    rw [← a.extend_at_source hρκ i, ← b.extend_at_source hρκ i]
    exact BoundedFamily.abs_sub_apply_le_dist (a.extend hρκ).val (b.extend hρκ).val _

theorem extend_mix (hρκ : ρ ≤ κ) (a b : Profile (OrdinalIndex ρ)) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    (a.mix b r s hr hs hrs).extend hρκ =
      (a.extend hρκ).mix (b.extend hρκ) r s hr hs hrs := by
  classical
  letI : TopologicalSpace (OrdinalIndex κ) := ⊥
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro i
  by_cases hi : i.val < ρ
  · simp only [extend_apply_lt hρκ _ i hi, mix_apply]
  · have hge := le_of_not_gt hi
    simp only [extend_apply_ge hρκ _ i hge, mix_apply, tail_mix]

end BFPP.Profile
