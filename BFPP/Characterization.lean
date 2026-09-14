import BFPP.Necessity
import BFPP.EDSupremum
import BFPP.BallOrderGeometry
import BFPP.LatticeFixedPoint

/-! # Characterization of the ball fixed point property for C(K, ℝ) -/

namespace BFPP

set_option autoImplicit false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem hasBFPP_of_extremallyDisconnected [ExtremallyDisconnected K] : HasBFPP C(K, ℝ) := by
  letI : CompleteLattice (UnitBall C(K, ℝ)) := edBallCompleteLattice
  intro T hT
  apply fixedPoint_of_interval_balls ?_ continuousBall_midpoint_radius T hT
  intro x r hr
  exact ⟨ballLower x r hr, ballUpper x r hr, continuousBall_closedBall_eq_Icc x r hr⟩

/-- Main characterization, with both implications proved from mathlib. -/
theorem hasBFPP_iff_extremallyDisconnected [T2Space K] :
    HasBFPP C(K, ℝ) ↔ ExtremallyDisconnected K := by
  refine ⟨extremallyDisconnected_of_hasBFPP, ?_⟩
  intro h
  letI : ExtremallyDisconnected K := h
  exact hasBFPP_of_extremallyDisconnected

theorem not_ED_iff_exists_fixedPointFree [T2Space K] :
    ¬ ExtremallyDisconnected K ↔
      ∃ T : UnitBall C(K, ℝ) → UnitBall C(K, ℝ), LipschitzWith 1 T ∧ ∀ f, T f ≠ f := by
  refine ⟨exists_nonexpansive_fixedPointFree_of_not_ED, ?_⟩
  rintro ⟨T, hT, hfree⟩ hED
  exact not_hasBFPP_of_fixedPointFree T hT hfree (hasBFPP_iff_extremallyDisconnected.mpr hED)

end BFPP
