import Mathlib.Order.Zorn
import Mathlib.Order.Bounds.Basic

/-! # Detecting incompleteness by a chain -/

namespace BFPP

set_option autoImplicit false
open Set

variable {B : Type*} [SemilatticeSup B]

/-- Chain completeness implies completeness in a join semilattice.
The empty chain is included in the hypothesis. -/
theorem exists_isLUB_of_chain_complete
    (hchain : ∀ c : Set B, IsChain (· ≤ ·) c → ∃ b, IsLUB c b) (s : Set B) :
    ∃ b, IsLUB s b := by
  let L := lowerBounds (upperBounds s)
  obtain ⟨m, hm⟩ := zorn_le₀ L (by
    intro c hc hcc
    obtain ⟨b, hb⟩ := hchain c hcc
    refine ⟨b, ?_, fun z hz => hb.1 hz⟩
    intro u hu
    exact hb.2 (fun z hz => hc hz hu))
  refine ⟨m, ?_, hm.prop⟩
  intro x hx
  have hxL : x ∈ L := fun u hu => hu hx
  have hsup : m ⊔ x ∈ L := fun u hu => sup_le (hm.prop hu) (hxL hu)
  exact le_sup_right.trans (hm.2 hsup le_sup_left)

theorem exists_chain_without_isLUB (h : ∃ s : Set B, ¬ ∃ b, IsLUB s b) :
    ∃ c : Set B, IsChain (· ≤ ·) c ∧ ¬ ∃ b, IsLUB c b := by
  classical
  by_contra hn
  have hall : ∀ c : Set B, IsChain (· ≤ ·) c → ∃ b, IsLUB c b := by
    intro c hc
    by_contra hb
    exact hn ⟨c, hc, hb⟩
  obtain ⟨s, hs⟩ := h
  exact hs (exists_isLUB_of_chain_complete hall s)

end BFPP
