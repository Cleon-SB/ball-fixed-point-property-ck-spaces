import BFPP.PointwiseSupremum

/-! # Algebra of increasing pointwise prefixes -/

namespace BFPP

set_option autoImplicit false
open Set Order Cardinal unitInterval

universe u v w
variable {K : Type u} [TopologicalSpace K]
variable {ι : Type v} [LinearOrder ι]

noncomputable def pointwisePrefix (g : ι → C(K, I)) (i : ι) (t : K) : I := ⨆ j < i, g j t

theorem pointwisePrefix_image (g : ι → C(K, I)) (i : ι) :
    pointwisePrefix g i = pointwiseSup (g '' Iio i) := by
  funext t
  simp only [pointwisePrefix, pointwiseSup, iSup_image, mem_Iio]

theorem pointwisePrefix_mono (g : ι → C(K, I)) : Monotone (pointwisePrefix g) := by
  intro i j hij t
  exact iSup_le fun k => iSup_le fun hk =>
    le_iSup_of_le k (le_iSup_of_le (hk.trans_le hij) le_rfl)

theorem pointwisePrefix_bot [OrderBot ι] (g : ι → C(K, I)) :
    pointwisePrefix g ⊥ = fun _ => 0 := by
  funext t
  simp only [pointwisePrefix, not_lt_bot, iSup_false, iSup_bot]
  rfl

theorem pointwisePrefix_limit (g : ι → C(K, I)) (i : ι)
    (hi : ∀ j, j < i → ∃ k, j < k ∧ k < i) (t : K) :
    pointwisePrefix g i t = ⨆ j : Iio i, pointwisePrefix g j.val t := by
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    obtain ⟨k, hjk, hki⟩ := hi j hj
    exact le_iSup_of_le ⟨k, hki⟩ (le_iSup_of_le j (le_iSup_of_le hjk le_rfl))
  · exact iSup_le fun j => pointwisePrefix_mono g j.property.le t

theorem pointwisePrefix_terminal [NoMaxOrder ι] (g : ι → C(K, I)) (t : K) :
    (⨆ i, pointwisePrefix g i t) = ⨆ i, g i t := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun j => iSup_le fun _ => le_iSup (fun j => g j t) j
  · refine iSup_le fun j => ?_
    obtain ⟨i, hji⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hji le_rfl))

theorem pointwisePrefix_reindex {ν : Type w} [LinearOrder ν] (e : ν ≃o ι)
    (g : ι → C(K, I)) (i : ν) :
    pointwisePrefix (g ∘ e) i = pointwisePrefix g (e i) := by
  funext t
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_iSup_of_le (e j) (le_iSup_of_le (e.strictMono hj) le_rfl)
  · refine iSup_le fun j => iSup_le fun hj => ?_
    have hji : e.symm j < i := by simpa using e.symm.strictMono hj
    exact le_iSup_of_le (e.symm j) (le_iSup_of_le hji (by simp))

end BFPP
