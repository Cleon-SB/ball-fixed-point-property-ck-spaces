import BFPP.OrdinalCofinality
import BFPP.ClopenPairs
import BFPP.CountablePairs
import Mathlib.SetTheory.Cardinal.Regular

/-! # Regular uncountable ordinal lengths for the main realization -/

namespace BFPP

set_option autoImplicit false
open Set Order Cardinal

universe u

structure RegularOrdinalPair (K : Type u) [TopologicalSpace K] where
  positiveLength : Ordinal.{u}
  negativeLength : Ordinal.{u}
  positiveLimit : IsSuccLimit positiveLength
  negativeLimit : IsSuccLimit negativeLength
  positiveRegular : positiveLength.cof.ord = positiveLength
  negativeRegular : negativeLength.cof.ord = negativeLength
  families : @InseparablePair K (OrdinalIndex positiveLength) (OrdinalIndex negativeLength) _ _
    (@ordinalIndexOrderBot positiveLength ⟨positiveLimit⟩) _
    (@ordinalIndexOrderBot negativeLength ⟨negativeLimit⟩)

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem exists_regularOrdinalPair (hF : IsFSpace K) (hED : ¬ ExtremallyDisconnected K) :
    Nonempty (RegularOrdinalPair K) := by
  by_cases hsep : TotallySeparatedSpace K
  · letI : TotallySeparatedSpace K := hsep
    obtain ⟨g⟩ := exists_clopen_chainGap hED
    obtain ⟨ρ, σ, hρ, hσ, hregρ, hregσ, g'⟩ := g.exists_indexedGap
    letI : Fact (IsSuccLimit ρ) := ⟨hρ⟩
    letI : Fact (IsSuccLimit σ) := ⟨hσ⟩
    exact ⟨⟨ρ, σ, hρ, hσ, hregρ, hregσ, g'.some.toInseparablePair⟩⟩
  · obtain ⟨ρ, hρ, hreg, F⟩ := exists_regular_pair_of_not_totallySeparated hF hsep
    exact ⟨⟨ρ, ρ, hρ, hρ, hreg, hreg, F.some⟩⟩

theorem countable_ordinalIndex_of_card_le_aleph0 (ρ : Ordinal.{u}) (hρ : ρ.card ≤ ℵ₀) :
    Countable (OrdinalIndex ρ) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_Iio_ordinal]
  simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.mpr hρ

namespace RegularOrdinalPair

noncomputable def length (R : RegularOrdinalPair K) : Ordinal.{u} := max R.positiveLength R.negativeLength

theorem length_isLimit (R : RegularOrdinalPair K) : IsSuccLimit R.length := by
  rcases le_total R.positiveLength R.negativeLength with h | h
  · simpa only [length, max_eq_right h] using R.negativeLimit
  · simpa only [length, max_eq_left h] using R.positiveLimit

theorem length_regular (R : RegularOrdinalPair K) : R.length.cof.ord = R.length := by
  rcases le_total R.positiveLength R.negativeLength with h | h
  · simpa only [length, max_eq_right h] using R.negativeRegular
  · simpa only [length, max_eq_left h] using R.positiveRegular

theorem length_card_eq_cof (R : RegularOrdinalPair K) : R.length.card = R.length.cof := by
  have h := congrArg Ordinal.card R.length_regular
  simpa using h.symm

theorem length_isInitial (R : RegularOrdinalPair K) : R.length.card.ord = R.length := by
  rw [R.length_card_eq_cof]
  exact R.length_regular

theorem length_card_isRegular (R : RegularOrdinalPair K) : R.length.card.IsRegular := by
  rw [R.length_card_eq_cof]
  exact Cardinal.isRegular_cof R.length_isLimit

theorem length_uncountable (R : RegularOrdinalPair K) (hF : IsFSpace K) : ℵ₀ < R.length.card := by
  by_contra h
  have hcount : R.length.card ≤ ℵ₀ := le_of_not_gt h
  have hp : R.positiveLength.card ≤ ℵ₀ :=
    (Ordinal.card_le_card (le_max_left _ _)).trans hcount
  have hn : R.negativeLength.card ≤ ℵ₀ :=
    (Ordinal.card_le_card (le_max_right _ _)).trans hcount
  letI : Fact (IsSuccLimit R.positiveLength) := ⟨R.positiveLimit⟩
  letI : Fact (IsSuccLimit R.negativeLength) := ⟨R.negativeLimit⟩
  letI : Countable (OrdinalIndex R.positiveLength) := countable_ordinalIndex_of_card_le_aleph0 _ hp
  letI : Countable (OrdinalIndex R.negativeLength) := countable_ordinalIndex_of_card_le_aleph0 _ hn
  exact R.families.false_of_countable_channels hF

end RegularOrdinalPair
end BFPP
