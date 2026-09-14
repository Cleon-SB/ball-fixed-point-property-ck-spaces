import BFPP.BooleanGap
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sets.Closeds

/-! # Completeness of clopens detects extremal disconnectedness -/

namespace BFPP

set_option autoImplicit false
open Set TopologicalSpace

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]

theorem extremallyDisconnected_of_clopen_complete
    (h : ∀ S : Set (Clopens K), ∃ H, IsLUB S H) : ExtremallyDisconnected K := by
  classical
  refine ⟨fun U hU => ?_⟩
  let S : Set (Clopens K) := {C | (C : Set K) ⊆ U}
  obtain ⟨H, hH⟩ := h S
  have hUH : U ⊆ H := by
    intro t ht
    obtain ⟨V, hV, htV, hVU⟩ := compact_exists_isClopen_in_isOpen hU ht
    exact hH.1 (show (⟨V, hV⟩ : Clopens K) ∈ S from hVU) htV
  have hcH : closure U ⊆ H := closure_minimal hUH H.isClosed
  have hHc : (H : Set K) ⊆ closure U := by
    intro t ht
    by_contra htc
    obtain ⟨V, hV, htV, hVc⟩ := compact_exists_isClopen_in_isOpen
      isClosed_closure.isOpen_compl htc
    let V' : Clopens K := ⟨V, hV⟩
    have hub : H ⊓ V'ᶜ ∈ upperBounds S := by
      intro C hC
      refine le_inf (hH.1 hC) ?_
      intro x hx hxV
      exact hVc hxV (subset_closure (hC hx))
    have hle := hH.2 hub
    have ht' : t ∈ H ⊓ V'ᶜ := hle ht
    exact ht'.2 htV
  have he : closure U = (H : Set K) := hcH.antisymm hHc
  rw [he]
  exact H.isOpen

theorem exists_clopen_chainGap (h : ¬ ExtremallyDisconnected K) :
    Nonempty (ChainGap (Clopens K)) := by
  classical
  apply exists_chainGap
  by_contra hn
  apply h
  apply extremallyDisconnected_of_clopen_complete
  intro S
  by_contra hS
  exact hn ⟨S, hS⟩

end BFPP
