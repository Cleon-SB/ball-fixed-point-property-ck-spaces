import BFPP.Deficits
import BFPP.TwoProfiles

/-! # The two-channel analysis map -/

namespace BFPP

set_option autoImplicit false

open Set

universe u v w
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
variable {ι : Type v} {κ : Type w}
  [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

def continuousBallNeg (f : UnitBall C(K, ℝ)) : UnitBall C(K, ℝ) :=
  ⟨-f.val, by simpa only [norm_neg] using f.property⟩

@[simp] theorem continuousBallNeg_apply (f : UnitBall C(K, ℝ)) (t : K) :
    (continuousBallNeg f).val t = -f.val t := rfl

theorem continuousBallNeg_isometry : Isometry (continuousBallNeg : UnitBall C(K, ℝ) → _) := by
  apply Isometry.of_dist_eq
  intro f g
  change dist (-f.val) (-g.val) = dist f.val g.val
  exact dist_neg_neg _ _

/-- The level-set data needed by analysis; no synthesis operator is assumed. -/
structure InseparableLevels (K : Type u) (ι : Type v) (κ : Type w)
    [TopologicalSpace K] [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ] where
  positive : ι → Set K
  negative : κ → Set K
  positive_mono : Monotone positive
  negative_mono : Monotone negative
  positive_bot : positive ⊥ = ∅
  negative_bot : negative ⊥ = ∅
  inseparable : (closure (⋃ i, positive i) ∩ closure (⋃ j, negative j)).Nonempty

namespace InseparableLevels

noncomputable def analyze (F : InseparableLevels K ι κ) (f : UnitBall C(K, ℝ)) :
    TwoProfile ι κ := by
  let a := analysisProfile F.positive F.positive_mono F.positive_bot f
  let b := analysisProfile F.negative F.negative_mono F.negative_bot (continuousBallNeg f)
  refine ⟨(a, b), ?_⟩
  obtain ⟨p, hp, hp'⟩ := F.inseparable
  have ha : 1 - f.val p ≤ a.tail :=
    analysisProfile_tail_at_closure _ _ _ _ p hp
  have hb : 1 + f.val p ≤ b.tail := by
    simpa only [continuousBallNeg_apply, sub_neg_eq_add] using
      analysisProfile_tail_at_closure F.negative F.negative_mono F.negative_bot
        (continuousBallNeg f) p hp'
  linarith

@[simp] theorem analyze_positive (F : InseparableLevels K ι κ) (f : UnitBall C(K, ℝ)) (i : ι) :
    (F.analyze f).val.1.val i = deficit (F.positive i) f := rfl

@[simp] theorem analyze_negative (F : InseparableLevels K ι κ) (f : UnitBall C(K, ℝ)) (j : κ) :
    (F.analyze f).val.2.val j = deficit (F.negative j) (continuousBallNeg f) := rfl

theorem analyze_nonexpansive (F : InseparableLevels K ι κ) : LipschitzWith 1 F.analyze := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  change max (dist (analysisProfile F.positive F.positive_mono F.positive_bot f)
    (analysisProfile F.positive F.positive_mono F.positive_bot g))
    (dist (analysisProfile F.negative F.negative_mono F.negative_bot (continuousBallNeg f))
      (analysisProfile F.negative F.negative_mono F.negative_bot (continuousBallNeg g))) ≤ dist f g
  apply max_le
  · simpa only [NNReal.coe_one, one_mul] using
      (analysisProfile_nonexpansive F.positive F.positive_mono F.positive_bot).dist_le_mul f g
  · have h := (analysisProfile_nonexpansive F.negative F.negative_mono F.negative_bot).dist_le_mul
      (continuousBallNeg f) (continuousBallNeg g)
    have hd : dist (continuousBallNeg f) (continuousBallNeg g) = dist f g :=
      dist_neg_neg f.val g.val
    simpa only [NNReal.coe_one, one_mul, hd] using h

theorem analyze_le_of_bounds (F : InseparableLevels K ι κ) (f : UnitBall C(K, ℝ))
    (z : TwoProfile ι κ)
    (hp : ∀ i t, t ∈ F.positive i → 1 - z.val.1.val i ≤ f.val t)
    (hn : ∀ j t, t ∈ F.negative j → f.val t ≤ z.val.2.val j - 1) : F.analyze f ≤ z := by
  constructor
  · intro i
    apply deficit_le_of_pointwise _ _ _ (z.val.1.nonneg i)
    intro t ht
    have h := hp i t ht
    linarith
  · intro j
    apply deficit_le_of_pointwise _ _ _ (z.val.2.nonneg j)
    intro t ht
    simp only [continuousBallNeg_apply]
    have h := hn j t ht
    linarith

/-- The synthesis construction must supply the map and the two level-set bounds. -/
theorem contractive_realization [NoMaxOrder ι] [NoMaxOrder κ]
    [WellFoundedLT ι] [WellFoundedLT κ]
    (F : InseparableLevels K ι κ) (J : TwoProfile ι κ → UnitBall C(K, ℝ))
    (hJ : LipschitzWith 1 J)
    (hp : ∀ z i t, t ∈ F.positive i → 1 - z.val.1.val i ≤ (J z).val t)
    (hn : ∀ z j t, t ∈ F.negative j → (J z).val t ≤ z.val.2.val j - 1) :
    LipschitzWith 1 (fun f => J ((F.analyze f).delay)) ∧
      ∀ f, J ((F.analyze f).delay) ≠ f :=
  BFPP.contractive_realization F.analyze J TwoProfile.delay F.analyze_nonexpansive hJ
    TwoProfile.delay_nonexpansive (fun z => F.analyze_le_of_bounds (J z) z (hp z) (hn z))
    TwoProfile.no_subsolution

end InseparableLevels
end BFPP
