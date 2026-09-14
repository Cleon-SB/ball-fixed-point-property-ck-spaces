import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLattice.Basic

/-! # Minimal invariant order intervals in a complete lattice -/

namespace BFPP

set_option autoImplicit false
open Set

variable {A : Type*} [CompleteLattice A]

def InvariantInterval (T : A → A) (s : Set A) : Prop :=
  ∃ l u, l ≤ u ∧ s = Icc l u ∧ MapsTo T s s

theorem invariantInterval_iInter (T : A → A) (c : Set (Set A))
    (hc : ∀ s ∈ c, InvariantInterval T s) (hchain : IsChain (· ⊆ ·) c) :
    InvariantInterval T (⋂ s : c, s.val) := by
  classical
  choose l u hlu heq hT using fun s : c => hc s.val s.property
  let L := ⨆ s : c, l s
  let U := ⨅ s : c, u s
  have hcross : ∀ s t : c, l s ≤ u t := by
    intro s t
    rcases hchain.total s.property t.property with hst | hts
    · have hls : l s ∈ s.val := by rw [heq s]; exact ⟨le_rfl, hlu s⟩
      have hlt := hst hls
      rw [heq t] at hlt
      exact hlt.2
    · have hut : u t ∈ t.val := by rw [heq t]; exact ⟨hlu t, le_rfl⟩
      have hus := hts hut
      rw [heq s] at hus
      exact hus.1
  have hLU : L ≤ U := iSup_le (fun s => le_iInf (hcross s))
  have hI : (⋂ s : c, s.val) = Icc L U := by
    ext x
    simp only [mem_iInter, heq, mem_Icc]
    constructor
    · intro hx
      exact ⟨iSup_le (fun s => (hx s).1), le_iInf (fun s => (hx s).2)⟩
    · intro hx s
      exact ⟨(le_iSup l s).trans hx.1, hx.2.trans (iInf_le u s)⟩
  refine ⟨L, U, hLU, hI, ?_⟩
  intro x hx
  simp only [mem_iInter] at hx ⊢
  intro s
  exact hT s (hx s)

theorem exists_minimal_invariant_interval (T : A → A) :
    ∃ l u, l ≤ u ∧ MapsTo T (Icc l u) (Icc l u) ∧
      ∀ a b, a ≤ b → Icc a b ⊆ Icc l u → MapsTo T (Icc a b) (Icc a b) →
        Icc l u ⊆ Icc a b := by
  classical
  obtain ⟨s, hs⟩ := zorn_superset {s | InvariantInterval T s} (by
    intro c hc hchain
    refine ⟨⋂ t : c, t.val, invariantInterval_iInter T c (fun t ht => hc ht) hchain, ?_⟩
    intro t ht x hx
    exact mem_iInter.mp hx ⟨t, ht⟩)
  obtain ⟨l, u, hlu, heq, hT⟩ := hs.prop
  refine ⟨l, u, hlu, heq ▸ hT, ?_⟩
  intro a b hab hsub hTab
  have hi : InvariantInterval T (Icc a b) := ⟨a, b, hab, rfl, hTab⟩
  have hrev := hs.2 hi (heq.symm ▸ hsub)
  exact heq ▸ hrev

end BFPP
