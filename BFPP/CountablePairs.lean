import BFPP.Cozero
import BFPP.Families
import Mathlib.Data.Countable.Defs

/-! # An inseparable pair on an F-space cannot have two countable channels -/

namespace BFPP

set_option autoImplicit false
open Set

universe u v w
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

theorem countable_union_cozero_indexed {ι : Type v} [Countable ι] (f : ι → C(K, ℝ)) :
    ∃ g : C(K, ℝ), {t | g t ≠ 0} = ⋃ i, {t | f i t ≠ 0} := by
  classical
  letI := Encodable.ofCountable ι
  let h : ℕ → C(K, ℝ) := fun n => (Encodable.decode (α := ι) n).elim 0 f
  obtain ⟨g, hg⟩ := countable_union_cozero h
  refine ⟨g, hg.trans ?_⟩
  ext t
  simp only [mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn⟩
    cases he : Encodable.decode (α := ι) n with
    | none => simp [h, he] at hn
    | some i => exact ⟨i, by simpa only [h, he, Option.elim_some] using hn⟩
  · rintro ⟨i, hi⟩
    exact ⟨Encodable.encode i, by simpa [h] using hi⟩

theorem InseparablePair.false_of_countable_channels
    {ι : Type v} {κ : Type w} [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]
    [Countable ι] [Countable κ] (F : InseparablePair K ι κ) (hK : IsFSpace K) : False := by
  obtain ⟨f, hf⟩ := countable_union_cozero_indexed F.positive.functions
  obtain ⟨g, hg⟩ := countable_union_cozero_indexed F.negative.functions
  have hdis : Disjoint {t | f t ≠ 0} {t | g t ≠ 0} := by
    rw [hf, hg]
    apply Set.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht'
    exact (mul_ne_zero hi hj) (F.orthogonal i j t)
  have hdis' := hK f g hdis
  rw [hf, hg] at hdis'
  have hp : (⋃ i, F.positive.levels i) ⊆ ⋃ i, {t | F.positive.functions i t ≠ 0} := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change F.positive.functions i t = 1 at hi
    change F.positive.functions i t ≠ 0
    rw [hi]
    norm_num
  have hn : (⋃ j, F.negative.levels j) ⊆ ⋃ j, {t | F.negative.functions j t ≠ 0} := by
    intro t ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    refine mem_iUnion.mpr ⟨j, ?_⟩
    change F.negative.functions j t = 1 at hj
    change F.negative.functions j t ≠ 0
    rw [hj]
    norm_num
  exact (Set.not_disjoint_iff.mpr F.inseparable) (hdis'.mono (closure_mono hp) (closure_mono hn))

end BFPP
