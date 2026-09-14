import BFPP.ContinuousBall
import BFPP.Profiles

/-! # Deficits over level sets, with the empty-set convention -/

namespace BFPP

set_option autoImplicit false

open Set

universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

noncomputable def deficit (s : Set K) (f : UnitBall C(K, ℝ)) : ℝ := by
  classical
  exact if s.Nonempty then ⨆ t : s, 1 - f.val t.val else 0

theorem deficit_range_bddAbove (s : Set K) (f : UnitBall C(K, ℝ)) :
    BddAbove (range (fun t : s => 1 - f.val t.val)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨t, rfl⟩
  have h := (continuousBall_bounds f t.val).1
  linarith

theorem deficit_nonneg (s : Set K) (f : UnitBall C(K, ℝ)) : 0 ≤ deficit s f := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨t, ht⟩ := hs
    rw [deficit, if_pos ⟨t, ht⟩]
    have h : 0 ≤ 1 - f.val t := sub_nonneg.mpr (continuousBall_bounds f t).2
    exact h.trans (le_ciSup (deficit_range_bddAbove s f) ⟨t, ht⟩)
  · simp [deficit, hs]

theorem deficit_le_two (s : Set K) (f : UnitBall C(K, ℝ)) : deficit s f ≤ 2 := by
  classical
  by_cases hs : s.Nonempty
  · letI : Nonempty s := hs.to_subtype
    rw [deficit, if_pos hs]
    apply ciSup_le
    intro t
    have h := (continuousBall_bounds f t.val).1
    linarith
  · simp [deficit, hs]

@[simp] theorem deficit_empty (f : UnitBall C(K, ℝ)) : deficit ∅ f = 0 := by
  simp [deficit]

theorem le_deficit (s : Set K) (f : UnitBall C(K, ℝ)) (t : K) (ht : t ∈ s) :
    1 - f.val t ≤ deficit s f := by
  classical
  rw [deficit, if_pos ⟨t, ht⟩]
  exact le_ciSup (deficit_range_bddAbove s f) ⟨t, ht⟩

theorem deficit_le_of_pointwise (s : Set K) (f : UnitBall C(K, ℝ))
    (a : ℝ) (ha : 0 ≤ a) (h : ∀ t ∈ s, 1 - f.val t ≤ a) : deficit s f ≤ a := by
  classical
  by_cases hs : s.Nonempty
  · letI : Nonempty s := hs.to_subtype
    rw [deficit, if_pos hs]
    exact ciSup_le (fun t => h t.val t.property)
  · simpa [deficit, hs] using ha

theorem deficit_mono (s t : Set K) (hst : s ⊆ t) (f : UnitBall C(K, ℝ)) :
    deficit s f ≤ deficit t f :=
  deficit_le_of_pointwise s f _ (deficit_nonneg t f)
    (fun x hx => le_deficit t f x (hst hx))

theorem deficit_nonexpansive (s : Set K) :
    LipschitzWith 1 (deficit s : UnitBall C(K, ℝ) → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  classical
  by_cases hs : s.Nonempty
  · letI : Nonempty s := hs.to_subtype
    simp only [deficit, if_pos hs]
    apply abs_ciSup_sub_ciSup_le _ _ (deficit_range_bddAbove s f) (deficit_range_bddAbove s g)
    intro t
    calc
      |1 - f.val t.val - (1 - g.val t.val)| = |g.val t.val - f.val t.val| := by
        congr 1
        ring
      _ = |f.val t.val - g.val t.val| := abs_sub_comm _ _
      _ ≤ dist f g := continuousMap_abs_sub_le_dist f.val g.val t.val
  · simpa [deficit, hs] using (dist_nonneg : 0 ≤ dist f g)

variable {ι : Type v} [LinearOrder ι] [OrderBot ι]

noncomputable def analysisProfile (F : ι → Set K) (hF : Monotone F) (hF₀ : F ⊥ = ∅)
    (f : UnitBall C(K, ℝ)) : Profile ι := by
  let a : BoundedFamily ι := BoundedFamily.ofBound (fun i => deficit (F i) f) 2
    (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (deficit_nonneg _ _)]
      exact deficit_le_two _ _)
  refine ⟨a, ?_, ?_, ?_⟩
  · change deficit (F ⊥) f = 0
    rw [hF₀, deficit_empty]
  · intro i j hij
    exact deficit_mono (F i) (F j) (hF hij) f
  · intro i
    exact ⟨deficit_nonneg _ _, deficit_le_two _ _⟩

@[simp] theorem analysisProfile_apply (F : ι → Set K) (hF : Monotone F)
    (hF₀ : F ⊥ = ∅) (f : UnitBall C(K, ℝ)) (i : ι) :
    (analysisProfile F hF hF₀ f).val i = deficit (F i) f := rfl

theorem analysisProfile_nonexpansive (F : ι → Set K) (hF : Monotone F) (hF₀ : F ⊥ = ∅) :
    LipschitzWith 1 (analysisProfile F hF hF₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  change dist (analysisProfile F hF hF₀ f).val (analysisProfile F hF hF₀ g).val ≤ dist f g
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).2
  intro i
  have h := (deficit_nonexpansive (F i)).dist_le_mul f g
  simpa only [analysisProfile_apply, NNReal.coe_one, one_mul, Real.dist_eq] using h

/-- Continuity extends the tail lower bound from the union to its closure. -/
theorem analysisProfile_tail_at_closure (F : ι → Set K) (hF : Monotone F)
    (hF₀ : F ⊥ = ∅) (f : UnitBall C(K, ℝ)) (p : K)
    (hp : p ∈ closure (⋃ i, F i)) : 1 - f.val p ≤ (analysisProfile F hF hF₀ f).tail := by
  let a := analysisProfile F hF hF₀ f
  have hc : IsClosed {t | 1 - f.val t ≤ a.tail} :=
    isClosed_le (continuous_const.sub f.val.continuous) continuous_const
  apply closure_minimal (t := {t | 1 - f.val t ≤ a.tail}) _ hc hp
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  exact (le_deficit (F i) f t hi).trans (a.le_tail i)

end BFPP
