import BFPP.Suprema
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bounded families with their genuine supremum metric

The index is given the discrete topology only inside this abbreviation.
It can independently carry an order topology elsewhere in the construction.
-/

namespace BFPP

set_option autoImplicit false

open Set

universe u

abbrev BoundedFamily (ι : Type u) :=
  @BoundedContinuousFunction ι ℝ ⊥ inferInstance

namespace BoundedFamily

variable {ι : Type u}

noncomputable def ofBound (f : ι → ℝ) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) :
    BoundedFamily ι := by
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  exact {
    toFun := f
    continuous_toFun := continuous_of_discreteTopology
    map_bounded' := ⟨2 * M, fun i j => by
      calc
        dist (f i) (f j) ≤ ‖f i‖ + ‖f j‖ := dist_le_norm_add_norm _ _
        _ ≤ 2 * M := by linarith [h i, h j]⟩ }

@[simp] theorem ofBound_apply (f : ι → ℝ) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) (i : ι) :
    ofBound f M h i = f i := rfl

theorem abs_apply_le_norm (f : BoundedFamily ι) (i : ι) : |f i| ≤ ‖f‖ := by
  letI : TopologicalSpace ι := ⊥
  simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm f i

theorem bddAbove_range (f : BoundedFamily ι) : BddAbove (range f) := by
  refine ⟨‖f‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (abs_le.mp (abs_apply_le_norm f i)).2

theorem bddBelow_range (f : BoundedFamily ι) : BddBelow (range f) := by
  refine ⟨-‖f‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (abs_le.mp (abs_apply_le_norm f i)).1

theorem abs_sub_apply_le_dist (f g : BoundedFamily ι) (i : ι) :
    |f i - g i| ≤ dist f g := by
  letI : TopologicalSpace ι := ⊥
  simpa only [Real.dist_eq] using
    BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) i

theorem dist_le_iff (f g : BoundedFamily ι) {d : ℝ} (hd : 0 ≤ d) :
    dist f g ≤ d ↔ ∀ i, |f i - g i| ≤ d := by
  letI : TopologicalSpace ι := ⊥
  simpa only [Real.dist_eq] using BoundedContinuousFunction.dist_le (f := f) (g := g) hd

theorem evaluation_nonexpansive (i : ι) :
    LipschitzWith 1 (fun f : BoundedFamily ι => f i) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_sub_apply_le_dist f g i

noncomputable def supremum (f : BoundedFamily ι) : ℝ := ⨆ i, f i

noncomputable def infimum (f : BoundedFamily ι) : ℝ := ⨅ i, f i

theorem supremum_nonexpansive [Nonempty ι] :
    LipschitzWith 1 (supremum : BoundedFamily ι → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, supremum] using
    abs_ciSup_sub_ciSup_le f g f.bddAbove_range g.bddAbove_range (dist f g)
      (abs_sub_apply_le_dist f g)

theorem infimum_nonexpansive [Nonempty ι] :
    LipschitzWith 1 (infimum : BoundedFamily ι → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, infimum] using
    abs_ciInf_sub_ciInf_le f g f.bddBelow_range g.bddBelow_range (dist f g)
      (abs_sub_apply_le_dist f g)

noncomputable def reindex {κ : Type*} (r : κ → ι) (f : BoundedFamily ι) :
    BoundedFamily κ := ofBound (fun j => f (r j)) ‖f‖
      (fun j => by simpa only [Real.norm_eq_abs] using abs_apply_le_norm f (r j))

@[simp] theorem reindex_apply {κ : Type*} (r : κ → ι) (f : BoundedFamily ι) (j : κ) :
    reindex r f j = f (r j) := rfl

theorem reindex_nonexpansive {κ : Type*} (r : κ → ι) :
    LipschitzWith 1 (reindex r : BoundedFamily ι → BoundedFamily κ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  apply (dist_le_iff _ _ dist_nonneg).2
  intro j
  exact abs_sub_apply_le_dist f g (r j)

end BoundedFamily
end BFPP
