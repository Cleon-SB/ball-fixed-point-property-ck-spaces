import BFPP.OrdinalIndex
import Mathlib.Topology.UnitInterval
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ExtremallyDisconnected

/-! # Discontinuous pointwise suprema and cardinal minimality -/

namespace BFPP

set_option autoImplicit false
open Set Order Cardinal unitInterval

universe u
variable {K : Type u} [TopologicalSpace K]

noncomputable def pointwiseSup (S : Set C(K, I)) (t : K) : I := ⨆ f ∈ S, f t

theorem pointwiseSup_mono {S T : Set C(K, I)} (h : S ⊆ T) : pointwiseSup S ≤ pointwiseSup T := by
  intro t
  exact iSup_le fun f => iSup_le fun hf => le_iSup_of_le f (le_iSup_of_le (h hf) le_rfl)

theorem pointwiseSup_finite (S : Set C(K, I)) (hS : S.Finite) : Continuous (pointwiseSup S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    have he : pointwiseSup (∅ : Set C(K, I)) = fun _ : K => (⊥ : I) := by
      funext t
      simp [pointwiseSup]
    rw [he]
    exact continuous_const
  | @insert f S hf hS ih =>
    have he : pointwiseSup (insert f S) = fun t => f t ⊔ pointwiseSup S t := by
      funext t
      apply le_antisymm
      · refine iSup_le fun g => iSup_le fun hg => ?_
        rcases hg with rfl | hg
        · exact le_sup_left
        · have hh : g t ≤ pointwiseSup S t := le_iSup_of_le g (le_iSup_of_le hg le_rfl)
          exact hh.trans le_sup_right
      · apply sup_le
        · exact le_iSup_of_le f (le_iSup_of_le (mem_insert f S) le_rfl)
        · exact pointwiseSup_mono (subset_insert f S) t
    rw [he]
    exact f.continuous.sup ih

def supportedUnitFunctions (U : Set K) : Set C(K, I) := {f | ∀ t, t ∉ U → f t = 0}

theorem pointwiseSup_supported_eq [CompactSpace K] [T2Space K] (U : Set K) (hU : IsOpen U) :
    pointwiseSup (supportedUnitFunctions U) = U.indicator (fun _ => (1 : I)) := by
  classical
  funext t
  by_cases ht : t ∈ U
  · rw [indicator_of_mem ht]
    apply top_unique
    obtain ⟨f, hf₀, hf₁, hb⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
      (isClosed_singleton (x := t)) (by
        rw [disjoint_singleton_right]
        simpa only [mem_compl_iff, not_not] using ht)
    let g : C(K, I) := ⟨fun x => ⟨f x, hb x⟩, f.continuous.subtype_mk _⟩
    have hg : g ∈ supportedUnitFunctions U := by
      intro x hx
      apply Subtype.ext
      exact hf₀ hx
    have hgt : g t = 1 := Subtype.ext (hf₁ (mem_singleton t))
    change (1 : I) ≤ ⨆ f ∈ supportedUnitFunctions U, f t
    rw [← hgt]
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  · rw [indicator_of_notMem ht]
    apply bot_unique
    exact iSup_le fun f => iSup_le fun hf => (hf t ht).le

theorem exists_discontinuous_pointwiseSup [CompactSpace K] [T2Space K]
    (U : Set K) (hU : IsOpen U) (hclosed : ¬ IsClosed U) :
    ∃ S : Set C(K, I), ¬ Continuous (pointwiseSup S) := by
  refine ⟨supportedUnitFunctions U, ?_⟩
  intro hc
  apply hclosed
  have he : (pointwiseSup (supportedUnitFunctions U)) ⁻¹' {1} = U := by
    rw [pointwiseSup_supported_eq U hU]
    ext t
    by_cases ht : t ∈ U <;> simp [ht]
  rw [← he]
  exact isClosed_singleton.preimage hc

theorem exists_open_not_closed_of_not_ED (hK : ¬ ExtremallyDisconnected K) :
    ∃ U : Set K, IsOpen U ∧ ¬ IsClosed U := by
  by_contra h
  have hall : ∀ U : Set K, IsOpen U → IsClosed U := by
    intro U hU
    by_contra hclosed
    exact h ⟨U, hU, hclosed⟩
  apply hK
  exact ⟨fun U hU => by rw [(hall U hU).closure_eq]; exact hU⟩

/-- Minimality is with respect to cardinality, not inclusion or ordinal length. -/
theorem exists_minimal_discontinuous_family [CompactSpace K] [T2Space K]
    (U : Set K) (hU : IsOpen U) (hclosed : ¬ IsClosed U) :
    ∃ S : Set C(K, I), ¬ Continuous (pointwiseSup S) ∧ ℵ₀ ≤ #S ∧
      ∀ T : Set C(K, I), #T < #S → Continuous (pointwiseSup T) := by
  obtain ⟨S, hS, hmin⟩ := (InvImage.wf (fun S : Set C(K, I) => #S) Cardinal.lt_wf).has_min
    {S | ¬ Continuous (pointwiseSup S)} (exists_discontinuous_pointwiseSup U hU hclosed)
  refine ⟨S, hS, ?_, ?_⟩
  · by_contra h
    have hfin : Finite S := Cardinal.lt_aleph0_iff_finite.mp (lt_of_not_ge h)
    exact hS (pointwiseSup_finite S (Set.toFinite S))
  · intro T hT
    by_contra hc
    exact hmin T hc hT

end BFPP
