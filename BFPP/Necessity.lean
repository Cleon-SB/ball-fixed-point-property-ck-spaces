import BFPP.ClopenPairs
import BFPP.SignRealization

/-! # Necessity of extremal disconnectedness for the ball fixed point property -/

namespace BFPP

set_option autoImplicit false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem not_hasBFPP_of_FSpace_not_ED (hF : IsFSpace K) (hED : ¬ ExtremallyDisconnected K) :
    ¬ HasBFPP C(K, ℝ) := by
  by_cases hsep : TotallySeparatedSpace K
  · letI : TotallySeparatedSpace K := hsep
    exact not_hasBFPP_of_zeroDimensional_not_ED hED
  · exact not_hasBFPP_of_not_totallySeparated hF hsep

/-- The necessity direction of the paper's characterization, including both topological cases. -/
theorem extremallyDisconnected_of_hasBFPP (h : HasBFPP C(K, ℝ)) : ExtremallyDisconnected K := by
  by_contra hED
  exact not_hasBFPP_of_FSpace_not_ED (isFSpace_of_hasBFPP h) hED h

theorem exists_nonexpansive_fixedPointFree_of_not_ED (hED : ¬ ExtremallyDisconnected K) :
    ∃ T : UnitBall C(K, ℝ) → UnitBall C(K, ℝ), LipschitzWith 1 T ∧ ∀ f, T f ≠ f := by
  classical
  by_contra hn
  apply hED
  apply extremallyDisconnected_of_hasBFPP
  intro T hT
  by_contra hfix
  apply hn
  exact ⟨T, hT, fun f hf => hfix ⟨f, hf⟩⟩

end BFPP
