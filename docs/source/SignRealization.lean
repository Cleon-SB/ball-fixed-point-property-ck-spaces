import BFPP.SignTermination
import BFPP.SaturatedChains
import BFPP.OrdinalIndex
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Realization of a stopped transfinite sign recursion -/

namespace BFPP

set_option autoImplicit false

open Set Order TopologicalSpace

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [NormalSpace K]

noncomputable def stoppedSignChain (seed : UnitBall C(K, ℝ)) (d : Ordinal.{u})
    [Fact (IsSuccLimit d)] (hd : ¬ SignStageGood seed d)
    (hbefore : ∀ a, a < d → SignStageGood seed a) :
    SaturatedSignChain K (OrdinalIndex d) where
  functions i := signRecursion seed i.val
  at_bot := by
    change (signRecursion seed 0).val = 0
    rw [signRecursion_zero]
    rfl
  positive i j hij t ht :=
    signRecursion_positive_saturated seed i.val j.val hij (hbefore j.val j.property) t ht
  negative i j hij t ht :=
    signRecursion_negative_saturated seed i.val j.val hij (hbefore j.val j.property) t ht
  terminal := by
    change (closure (signsPositiveBefore (signRecursion seed) d) ∩
      closure (signsNegativeBefore (signRecursion seed) d)).Nonempty
    exact Set.not_disjoint_iff.mp hd

theorem not_hasBFPP_of_clopenInseparable (hK : IsFSpace K)
    (seed : UnitBall C(K, ℝ)) (p q : K) (hpq : ClopenInseparable p q)
    (hp : seed.val p = 1) (hq : seed.val q = -1) : ¬ HasBFPP C(K, ℝ) := by
  obtain ⟨d, hlimit, hd, hbefore⟩ := exists_first_bad_limit hK seed p q hpq hp hq
  letI : Fact (IsSuccLimit d) := ⟨hlimit⟩
  exact (stoppedSignChain seed d hd hbefore).toInseparablePair.not_hasBFPP

theorem exists_clopenInseparable_of_not_totallySeparated
    (hK : ¬ TotallySeparatedSpace K) : ∃ p q : K, p ≠ q ∧ ClopenInseparable p q := by
  classical
  by_contra hnone
  apply hK
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro p q hpq
  have hsep : ¬ ClopenInseparable p q := by
    intro h
    exact hnone ⟨p, q, hpq, h⟩
  unfold ClopenInseparable at hsep
  push_neg at hsep
  obtain ⟨s, hp, hq⟩ := hsep
  exact ⟨s, s.isClopen, hp, hq⟩

theorem not_hasBFPP_of_not_totallySeparated [T2Space K] (hF : IsFSpace K)
    (hK : ¬ TotallySeparatedSpace K) : ¬ HasBFPP C(K, ℝ) := by
  obtain ⟨p, q, hpq, hinsep⟩ := exists_clopenInseparable_of_not_totallySeparated hK
  have hd : Disjoint (closure ({p} : Set K)) (closure ({q} : Set K)) := by
    simpa only [isClosed_singleton.closure_eq, disjoint_singleton] using hpq
  obtain ⟨seed, hp, hq⟩ := exists_sign_extension ({p} : Set K) {q} hd
  exact not_hasBFPP_of_clopenInseparable hF seed p q hinsep
    (hp p (subset_closure (mem_singleton p))) (hq q (subset_closure (mem_singleton q)))

theorem totallySeparated_of_hasBFPP [T2Space K] (h : HasBFPP C(K, ℝ)) :
    TotallySeparatedSpace K := by
  by_contra hn
  exact not_hasBFPP_of_not_totallySeparated (isFSpace_of_hasBFPP h) hn h

end BFPP
