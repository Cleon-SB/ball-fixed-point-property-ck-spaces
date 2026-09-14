import BFPP.CofinalReindexing
import BFPP.SignRealization
import Mathlib.SetTheory.Ordinal.FundamentalSequence

/-! # Regular cofinal lengths for the sign construction -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u

theorem exists_ordinal_cofinal_from_bot (τ : Ordinal.{u}) [hτ : Fact (IsSuccLimit τ)] :
    ∃ ρ : Ordinal.{u}, ∃ hρ : IsSuccLimit ρ, ρ.cof.ord = ρ ∧
      ∃ φ : Iio ρ → Iio τ, Monotone φ ∧ φ ⟨0, hρ.pos⟩ = ⊥ ∧ IsCofinal (range φ) := by
  classical
  let ρ := τ.cof.ord
  have hρ : IsSuccLimit ρ := by
    apply Ordinal.one_lt_cof_iff.mp
    change 1 < τ.cof.ord.cof
    rw [Ordinal.cof_ord_cof]
    exact Ordinal.one_lt_cof_iff.mpr hτ.out
  have hreg : ρ.cof.ord = ρ := by simp [ρ]
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq (o := τ) (a := ρ) rfl
  letI : Fact (IsSuccLimit ρ) := ⟨hρ⟩
  let φ : Iio ρ → Iio τ := fun i => if i.val = 0 then ⊥ else f i
  refine ⟨ρ, hρ, hreg, φ, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val = 0
    · simp only [φ, if_pos hi]
      exact bot_le
    · have hj : j.val ≠ 0 := by
        intro hj
        exact hi (le_antisymm (hj ▸ hij) bot_le)
      simpa only [φ, if_neg hi, if_neg hj] using hf.strictMono.monotone hij
  · simp [φ]
  · intro a
    obtain ⟨_, ⟨i, rfl⟩, hai⟩ := hf.isCofinal_range a
    obtain ⟨j, hij⟩ := exists_gt i
    have hj : j.val ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hij)
    refine ⟨φ j, mem_range_self j, ?_⟩
    simpa only [φ, if_neg hj] using hai.trans (hf.strictMono hij).le

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem exists_regular_pair_of_not_totallySeparated (hF : IsFSpace K)
    (hK : ¬ TotallySeparatedSpace K) :
    ∃ ρ : Ordinal.{u}, ∃ hρ : IsSuccLimit ρ, ρ.cof.ord = ρ ∧
      @Nonempty (@InseparablePair K (OrdinalIndex ρ) (OrdinalIndex ρ) _ _
        (@ordinalIndexOrderBot ρ ⟨hρ⟩) _ (@ordinalIndexOrderBot ρ ⟨hρ⟩)) := by
  obtain ⟨p, q, hpq, hinsep⟩ := exists_clopenInseparable_of_not_totallySeparated hK
  have hd : Disjoint (closure ({p} : Set K)) (closure ({q} : Set K)) := by
    simpa only [isClosed_singleton.closure_eq, disjoint_singleton] using hpq
  obtain ⟨seed, hp, hq⟩ := exists_sign_extension ({p} : Set K) {q} hd
  obtain ⟨d, hlimit, hd, hbefore⟩ := exists_first_bad_limit hF seed p q hinsep
    (hp p (subset_closure (mem_singleton p))) (hq q (subset_closure (mem_singleton q)))
  letI : Fact (IsSuccLimit d) := ⟨hlimit⟩
  let F := (stoppedSignChain seed d hd hbefore).toInseparablePair
  obtain ⟨ρ, hρ, hreg, φ, hφ, hφ₀, hcof⟩ := exists_ordinal_cofinal_from_bot d
  letI : Fact (IsSuccLimit ρ) := ⟨hρ⟩
  exact ⟨ρ, hρ, hreg, ⟨F.reindex φ φ hφ hφ hφ₀ hφ₀ hcof hcof⟩⟩

end BFPP
