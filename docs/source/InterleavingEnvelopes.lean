import BFPP.Interleaving
import BFPP.EnvelopeOrder
import Mathlib.Order.Cofinal

/-! # Separated interleaved channels are recovered by the two envelopes -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {κ : Ordinal.{u}} [Fact (IsSuccLimit κ)]

theorem evenIndex_cofinal : IsCofinal (range (evenIndex κ)) :=
  isCofinal_range_of_strictMono (evenIndex_strictMono κ)

theorem oddIndex_cofinal : IsCofinal (range (oddIndex κ)) :=
  isCofinal_range_of_strictMono (oddIndex_strictMono κ)

theorem halfIndex_monotone : Monotone (halfIndex κ) := by
  intro i j hij
  exact (Ordinal.mul_div_gc (by norm_num : (2 : Ordinal.{u}) ≠ 0)).monotone_u hij

theorem interleave_lowerEnvelope (a b : Profile (OrdinalIndex κ)) :
    lowerEnvelope (interleave a.val b.val) = a.tail := by
  apply le_antisymm
  · apply lowerEnvelope_le
    intro i
    obtain ⟨_, ⟨j, rfl⟩, hij⟩ := evenIndex_cofinal i
    calc
      lowerTail (interleave a.val b.val) i ≤ interleave a.val b.val (evenIndex κ j) :=
        lowerTail_le_point _ _ _ hij
      _ = a.val j := interleave_even _ _ _
      _ ≤ a.tail := a.le_tail j
  · apply ciSup_le
    intro j
    apply le_trans ?_ (lowerTail_le_lowerEnvelope (interleave a.val b.val) (evenIndex κ j))
    apply le_lowerTail
    intro i hji
    have hjhalf : j ≤ halfIndex κ i := by
      have h := halfIndex_monotone hji
      simpa only [half_evenIndex] using h
    rcases index_eq_even_or_odd κ i with he | ho
    · rw [he, interleave_even]
      exact a.monotone hjhalf
    · rw [ho, interleave_odd]
      have ha := a.le_two j
      have hb := b.nonneg (halfIndex κ i)
      linarith

theorem interleave_upperEnvelope (a b : Profile (OrdinalIndex κ)) :
    upperEnvelope (interleave a.val b.val) = 4 + b.tail := by
  apply le_antisymm
  · apply le_trans (upperEnvelope_le_upperTail (interleave a.val b.val) ⊥)
    apply upperTail_le
    intro i _
    rcases index_eq_even_or_odd κ i with he | ho
    · rw [he, interleave_even]
      have ha := a.le_two (halfIndex κ i)
      have hb := b.tail_nonneg
      linarith
    · rw [ho, interleave_odd]
      exact add_le_add le_rfl (b.le_tail _)
  · apply le_upperEnvelope
    intro i
    have h : b.tail ≤ upperTail (interleave a.val b.val) i - 4 := by
      apply ciSup_le
      intro j
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := oddIndex_cofinal (max i (oddIndex κ j))
      have hik : i ≤ oddIndex κ k := (le_max_left _ _).trans hk
      have hjk : j ≤ k := (oddIndex_strictMono κ).le_iff_le.mp ((le_max_right _ _).trans hk)
      have hpoint := point_le_upperTail (interleave a.val b.val) i (oddIndex κ k) hik
      rw [interleave_odd] at hpoint
      have hmono := b.monotone hjk
      linarith
    linarith

end BFPP
