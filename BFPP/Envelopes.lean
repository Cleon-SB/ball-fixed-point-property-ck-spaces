import BFPP.BoundedFamilies

/-!
# Upper and lower ordinal envelopes

The metric proof works on any nonempty preorder. Instantiating the index type
with the ordinals below a nonzero limit gives precisely Section 2.1 of the paper.
-/

namespace BFPP

set_option autoImplicit false

open Set

universe u
variable {ι : Type u} [Preorder ι]

noncomputable def upperTail (f : BoundedFamily ι) (b : ι) : ℝ :=
  BoundedFamily.supremum (BoundedFamily.reindex (fun j : Ici b => j.val) f)

noncomputable def lowerTail (f : BoundedFamily ι) (b : ι) : ℝ :=
  BoundedFamily.infimum (BoundedFamily.reindex (fun j : Ici b => j.val) f)

theorem abs_upperTail_le (f : BoundedFamily ι) (b : ι) : |upperTail f b| ≤ ‖f‖ := by
  letI : Nonempty (Ici b) := ⟨⟨b, le_rfl⟩⟩
  apply abs_le.mpr
  constructor
  · calc
      -‖f‖ ≤ f b := (abs_le.mp (f.abs_apply_le_norm b)).1
      _ ≤ upperTail f b :=
        le_ciSup (BoundedFamily.bddAbove_range
          (BoundedFamily.reindex (fun j : Ici b => j.val) f)) ⟨b, le_rfl⟩
  · apply ciSup_le
    intro j
    exact (abs_le.mp (f.abs_apply_le_norm j.val)).2

theorem abs_lowerTail_le (f : BoundedFamily ι) (b : ι) : |lowerTail f b| ≤ ‖f‖ := by
  letI : Nonempty (Ici b) := ⟨⟨b, le_rfl⟩⟩
  apply abs_le.mpr
  constructor
  · apply le_ciInf
    intro j
    exact (abs_le.mp (f.abs_apply_le_norm j.val)).1
  · calc
      lowerTail f b ≤ f b :=
        ciInf_le (BoundedFamily.bddBelow_range
          (BoundedFamily.reindex (fun j : Ici b => j.val) f)) ⟨b, le_rfl⟩
      _ ≤ ‖f‖ := (abs_le.mp (f.abs_apply_le_norm b)).2

noncomputable def upperTails (f : BoundedFamily ι) : BoundedFamily ι :=
  BoundedFamily.ofBound (upperTail f) ‖f‖ (abs_upperTail_le f)

noncomputable def lowerTails (f : BoundedFamily ι) : BoundedFamily ι :=
  BoundedFamily.ofBound (lowerTail f) ‖f‖ (abs_lowerTail_le f)

theorem upperTails_nonexpansive : LipschitzWith 1 (upperTails : BoundedFamily ι → _) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).2
  intro b
  letI : Nonempty (Ici b) := ⟨⟨b, le_rfl⟩⟩
  have h := (BoundedFamily.supremum_nonexpansive.comp
    (BoundedFamily.reindex_nonexpansive (fun j : Ici b => j.val))).dist_le_mul f g
  simpa only [NNReal.coe_mul, NNReal.coe_one, mul_one, one_mul,
    Real.dist_eq, upperTails, BoundedFamily.ofBound_apply, upperTail,
    Function.comp_def] using h

theorem lowerTails_nonexpansive : LipschitzWith 1 (lowerTails : BoundedFamily ι → _) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).2
  intro b
  letI : Nonempty (Ici b) := ⟨⟨b, le_rfl⟩⟩
  have h := (BoundedFamily.infimum_nonexpansive.comp
    (BoundedFamily.reindex_nonexpansive (fun j : Ici b => j.val))).dist_le_mul f g
  simpa only [NNReal.coe_mul, NNReal.coe_one, mul_one, one_mul,
    Real.dist_eq, lowerTails, BoundedFamily.ofBound_apply, lowerTail,
    Function.comp_def] using h

noncomputable def upperEnvelope (f : BoundedFamily ι) : ℝ :=
  BoundedFamily.infimum (upperTails f)

noncomputable def lowerEnvelope (f : BoundedFamily ι) : ℝ :=
  BoundedFamily.supremum (lowerTails f)

theorem upperEnvelope_nonexpansive [Nonempty ι] :
    LipschitzWith 1 (upperEnvelope : BoundedFamily ι → ℝ) := by
  change LipschitzWith 1 (fun f : BoundedFamily ι => BoundedFamily.infimum (upperTails f))
  simpa only [mul_one, Function.comp_def, upperEnvelope] using
    BoundedFamily.infimum_nonexpansive.comp upperTails_nonexpansive

theorem lowerEnvelope_nonexpansive [Nonempty ι] :
    LipschitzWith 1 (lowerEnvelope : BoundedFamily ι → ℝ) := by
  change LipschitzWith 1 (fun f : BoundedFamily ι => BoundedFamily.supremum (lowerTails f))
  simpa only [mul_one, Function.comp_def, lowerEnvelope] using
    BoundedFamily.supremum_nonexpansive.comp lowerTails_nonexpansive

end BFPP
