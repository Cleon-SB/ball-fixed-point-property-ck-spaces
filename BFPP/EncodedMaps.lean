import BFPP.EncodedDomain

/-! # Analysis, synthesis, and propagation on the encoded domain -/

namespace BFPP

set_option autoImplicit false
open Order

universe u v
variable {ρ σ κ : Ordinal.{u}} [Fact (IsSuccLimit ρ)] [Fact (IsSuccLimit σ)] [Fact (IsSuccLimit κ)]

noncomputable def encodedPropagator (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :
    EncodedDomain hρκ hσκ → EncodedDomain hρκ hσκ :=
  fun x => encodeIso hρκ hσκ ((encodeIso hρκ hσκ).symm x).delay

@[simp] theorem encodedPropagator_encode (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (z : TwoProfile (OrdinalIndex ρ) (OrdinalIndex σ)) :
    encodedPropagator hρκ hσκ (encodeIso hρκ hσκ z) = encodeIso hρκ hσκ z.delay := by
  simp only [encodedPropagator, IsometryEquiv.symm_apply_apply]

theorem encodedPropagator_nonexpansive (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ) :
    LipschitzWith 1 (encodedPropagator hρκ hσκ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  change dist (encodeIso hρκ hσκ ((encodeIso hρκ hσκ).symm x).delay)
    (encodeIso hρκ hσκ ((encodeIso hρκ hσκ).symm y).delay) ≤ dist x y
  rw [(encodeIso hρκ hσκ).dist_eq]
  have h := TwoProfile.delay_nonexpansive.dist_le_mul
    ((encodeIso hρκ hσκ).symm x) ((encodeIso hρκ hσκ).symm y)
  simpa only [NNReal.coe_one, one_mul, (encodeIso hρκ hσκ).symm.dist_eq] using h

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]

noncomputable def encodedAnalysis (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (F : InseparablePair K (OrdinalIndex ρ) (OrdinalIndex σ)) :
    UnitBall C(K, ℝ) → EncodedDomain hρκ hσκ :=
  fun f => encodeIso hρκ hσκ (F.levels.analyze f)

noncomputable def encodedSynthesis (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (F : InseparablePair K (OrdinalIndex ρ) (OrdinalIndex σ)) :
    EncodedDomain hρκ hσκ → UnitBall C(K, ℝ) :=
  fun x => F.synthesize ((encodeIso hρκ hσκ).symm x)

theorem encodedAnalysis_nonexpansive (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (F : InseparablePair K (OrdinalIndex ρ) (OrdinalIndex σ)) :
    LipschitzWith 1 (encodedAnalysis hρκ hσκ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  change dist (encodeIso hρκ hσκ (F.levels.analyze f))
    (encodeIso hρκ hσκ (F.levels.analyze g)) ≤ dist f g
  rw [(encodeIso hρκ hσκ).dist_eq]
  simpa only [NNReal.coe_one, one_mul] using F.levels.analyze_nonexpansive.dist_le_mul f g

theorem encodedSynthesis_nonexpansive (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (F : InseparablePair K (OrdinalIndex ρ) (OrdinalIndex σ)) :
    LipschitzWith 1 (encodedSynthesis hρκ hσκ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  have h := F.synthesize_nonexpansive.dist_le_mul ((encodeIso hρκ hσκ).symm x)
    ((encodeIso hρκ hσκ).symm y)
  simpa only [NNReal.coe_one, one_mul, (encodeIso hρκ hσκ).symm.dist_eq, encodedSynthesis] using h

theorem encoded_coefficient_fixedPointFree (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (F : InseparablePair K (OrdinalIndex ρ) (OrdinalIndex σ)) (x : EncodedDomain hρκ hσκ) :
    encodedAnalysis hρκ hσκ F (encodedSynthesis hρκ hσκ F (encodedPropagator hρκ hσκ x)) ≠ x := by
  intro he
  have he' := congrArg (encodeIso hρκ hσκ).symm he
  have hc : F.levels.analyze (F.synthesize ((encodeIso hρκ hσκ).symm x).delay) =
      (encodeIso hρκ hσκ).symm x := by
    simpa only [encodedAnalysis, encodedSynthesis, encodedPropagator,
      IsometryEquiv.symm_apply_apply] using he'
  have hle := F.analyze_synthesize_le ((encodeIso hρκ hσκ).symm x).delay
  rw [hc] at hle
  exact TwoProfile.no_subsolution _ hle

theorem encoded_ballMap_eq (hρκ : ρ ≤ κ) (hσκ : σ ≤ κ)
    (F : InseparablePair K (OrdinalIndex ρ) (OrdinalIndex σ)) :
    (fun f => encodedSynthesis hρκ hσκ F (encodedPropagator hρκ hσκ (encodedAnalysis hρκ hσκ F f))) =
      F.ballMap := by
  funext f
  simp only [encodedAnalysis, encodedSynthesis, encodedPropagator,
    IsometryEquiv.symm_apply_apply, InseparablePair.ballMap]

end BFPP
