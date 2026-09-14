import BFPP.IndexedGaps
import BFPP.ClopenCompleteness

/-! # Inseparable continuous families obtained from clopen gaps -/

namespace BFPP

set_option autoImplicit false
open Set TopologicalSpace

universe u v w
variable {K : Type u} [TopologicalSpace K]
  {ι : Type v} {κ : Type w} [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

noncomputable def clopenStep (C : Clopens K) : C(K, ℝ) :=
  ⟨(C : Set K).indicator (fun _ => 1), C.isClopen.continuous_indicator continuous_const⟩

@[simp] theorem clopenStep_apply (C : Clopens K) (t : K) [Decidable (t ∈ C)] :
    clopenStep C t = if t ∈ C then 1 else 0 := by
  classical
  change (C : Set K).indicator (fun _ => (1 : ℝ)) t = _
  by_cases h : t ∈ C <;> simp [Set.indicator, h]

noncomputable def clopenFamily (F : ι → Clopens K) (hm : Monotone F) (h₀ : F ⊥ = ⊥) :
    IncreasingFamily K ι where
  functions := fun i => clopenStep (F i)
  monotone t := by
    classical
    intro i j hij
    by_cases hi : t ∈ F i
    · have hj := hm hij hi
      simp [hi, hj]
    · simp only [clopenStep_apply, if_neg hi]
      split_ifs <;> norm_num
  bounds i t := by
    classical
    simp only [clopenStep_apply]
    split_ifs <;> norm_num
  at_bot := by
    classical
    ext t
    simp [h₀, clopenStep]

@[simp] theorem clopenFamily_levels (F : ι → Clopens K) (hm : Monotone F) (h₀ : F ⊥ = ⊥)
    (i : ι) : (clopenFamily F hm h₀).levels i = (F i : Set K) := by
  classical
  ext t
  change (if t ∈ F i then (1 : ℝ) else 0) = 1 ↔ t ∈ F i
  by_cases h : t ∈ F i <;> simp [h]

namespace IndexedGap

variable [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]

noncomputable def toInseparablePair (g : IndexedGap (Clopens K) ι κ) :
    InseparablePair K ι κ where
  positive := clopenFamily g.lower g.lower_mono g.lower_bot
  negative := clopenFamily (fun j => (g.upper j)ᶜ)
    (fun _ _ hij => compl_le_compl (g.upper_anti hij)) (by rw [g.upper_bot, compl_top])
  orthogonal i j t := by
    classical
    change clopenStep (g.lower i) t * clopenStep (g.upper j)ᶜ t = 0
    by_cases ht : t ∈ g.lower i
    · have ht' : t ∈ g.upper j := g.cross i j ht
      have ht'' : t ∉ (g.upper j)ᶜ := fun h => h ht'
      simp [ht, ht'']
    · simp [ht]
  inseparable := by
    classical
    simp only [clopenFamily_levels]
    apply Set.not_disjoint_iff.mp
    intro hd
    have hd' : Disjoint (closure (⋃ i, (g.lower i : Set K)))
        (closure (⋃ j, ((g.upper j)ᶜ : Set K))) := by
      refine hd.mono le_rfl (closure_mono ?_)
      intro t ht
      obtain ⟨j, hj⟩ := mem_iUnion.mp ht
      refine mem_iUnion.mpr ⟨j, ?_⟩
      change clopenStep (g.upper j)ᶜ t = 1
      rw [clopenStep_apply]
      exact if_pos (show t ∈ (g.upper j)ᶜ from hj)
    obtain ⟨C, hC, hUC, hCV⟩ := exists_clopen_of_closed_subset_open isClosed_closure
      isClosed_closure.isOpen_compl (Set.disjoint_left.mp hd')
    apply g.no_interpolant
    refine ⟨⟨C, hC⟩, ?_, ?_⟩
    · intro i t ht
      exact hUC (subset_closure (mem_iUnion.mpr ⟨i, ht⟩))
    · intro j t ht
      by_contra hn
      exact hCV ht (subset_closure (mem_iUnion.mpr ⟨j, hn⟩))

end IndexedGap

theorem not_hasBFPP_of_zeroDimensional_not_ED
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (h : ¬ ExtremallyDisconnected K) : ¬ HasBFPP C(K, ℝ) := by
  obtain ⟨g⟩ := exists_clopen_chainGap h
  obtain ⟨ρ, σ, hρ, hσ, _, _, g'⟩ := g.exists_indexedGap
  letI : Fact (Order.IsSuccLimit ρ) := ⟨hρ⟩
  letI : Fact (Order.IsSuccLimit σ) := ⟨hσ⟩
  exact g'.some.toInseparablePair.not_hasBFPP

end BFPP
