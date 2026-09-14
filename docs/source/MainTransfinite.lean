import BFPP.RegularPairs
import BFPP.EncodedRecurrence

/-! # The main single-ordinal transfinite realization theorem -/

namespace BFPP

set_option autoImplicit false
open Set Order Cardinal

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- An uncountable regular initial ordinal and all the actual realization maps.
No synthesis operator, inseparable pair, or fixed-point obstruction is assumed. -/
theorem exists_transfinite_realization (hF : IsFSpace K) (hED : ¬ ExtremallyDisconnected K) :
    ∃ κ : Ordinal.{u}, κ.card.ord = κ ∧ κ.card.IsRegular ∧ ℵ₀ < κ.card ∧
      ∃ D : Set (BoundedFamily (OrdinalIndex κ)),
        D.Nonempty ∧ IsClosed D ∧ Bornology.IsBounded D ∧ Convex ℝ D ∧
        ∃ (A : UnitBall C(K, ℝ) → D) (J : D → UnitBall C(K, ℝ)) (P : D → D),
          LipschitzWith 1 A ∧ LipschitzWith 1 J ∧ LipschitzWith 1 P ∧ IsTCP D P ∧
          (∀ z, A (J (P z)) ≠ z) ∧
          LipschitzWith 1 (fun f => J (P (A f))) ∧ (∀ f, J (P (A f)) ≠ f) := by
  obtain ⟨R⟩ := exists_regularOrdinalPair hF hED
  letI : Fact (IsSuccLimit R.positiveLength) := ⟨R.positiveLimit⟩
  letI : Fact (IsSuccLimit R.negativeLength) := ⟨R.negativeLimit⟩
  letI : Fact (IsSuccLimit R.length) := ⟨R.length_isLimit⟩
  have hp : R.positiveLength ≤ R.length := le_max_left _ _
  have hn : R.negativeLength ≤ R.length := le_max_right _ _
  refine ⟨R.length, R.length_isInitial, R.length_card_isRegular, R.length_uncountable hF,
    encodedSet hp hn, encodedSet_nonempty hp hn, encodedSet_isClosed hp hn,
    encodedSet_isBounded hp hn, encodedSet_convex hp hn,
    encodedAnalysis hp hn R.families, encodedSynthesis hp hn R.families,
    encodedPropagator hp hn, encodedAnalysis_nonexpansive hp hn R.families,
    encodedSynthesis_nonexpansive hp hn R.families, encodedPropagator_nonexpansive hp hn,
    encodedPropagator_isTCP hp hn, encoded_coefficient_fixedPointFree hp hn R.families, ?_, ?_⟩
  · exact nonexpansive_transfer _ _ _ (encodedAnalysis_nonexpansive hp hn R.families)
      (encodedSynthesis_nonexpansive hp hn R.families) (encodedPropagator_nonexpansive hp hn)
  · exact fixedPointFree_transfer _ _ _ (encoded_coefficient_fixedPointFree hp hn R.families)

end BFPP
