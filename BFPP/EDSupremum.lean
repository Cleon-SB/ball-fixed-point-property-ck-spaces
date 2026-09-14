import BFPP.ContinuousBall
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Ordered

/-! # Continuous lattice suprema on an extremally disconnected compact space -/

namespace BFPP

set_option autoImplicit false
open Set TopologicalSpace

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [ExtremallyDisconnected K]

def edCut (S : Set (UnitBall C(K, ℝ))) (q : ℝ) : Set K :=
  closure (⋃ f : S, {t | q < f.val.val t})

theorem edCut_isClopen (S : Set (UnitBall C(K, ℝ))) (q : ℝ) : IsClopen (edCut S q) :=
  ⟨isClosed_closure, ExtremallyDisconnected.open_closure _
    (isOpen_iUnion fun f => isOpen_lt continuous_const f.val.val.continuous)⟩

theorem edCut_antitone (S : Set (UnitBall C(K, ℝ))) : Antitone (edCut S) := by
  intro p q hpq
  apply closure_mono
  intro t ht
  obtain ⟨f, hf⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨f, lt_of_le_of_lt hpq hf⟩

def edSupValues (S : Set (UnitBall C(K, ℝ))) (t : K) : Set ℝ :=
  {-1} ∪ {q | q ∈ Icc (-1) 1 ∧ t ∈ edCut S q}

theorem edSupValues_nonempty (S : Set (UnitBall C(K, ℝ))) (t : K) :
    (edSupValues S t).Nonempty := ⟨-1, Or.inl rfl⟩

theorem edSupValues_bddAbove (S : Set (UnitBall C(K, ℝ))) (t : K) :
    BddAbove (edSupValues S t) := by
  refine ⟨1, ?_⟩
  rintro q (hq | hq)
  · have he : q = -1 := hq
    rw [he]
    norm_num
  · exact hq.1.2

noncomputable def edSupValue (S : Set (UnitBall C(K, ℝ))) (t : K) : ℝ := sSup (edSupValues S t)

theorem edSupValue_bounds (S : Set (UnitBall C(K, ℝ))) (t : K) :
    -1 ≤ edSupValue S t ∧ edSupValue S t ≤ 1 := by
  refine ⟨le_csSup (edSupValues_bddAbove S t) (Or.inl rfl), ?_⟩
  apply csSup_le (edSupValues_nonempty S t)
  rintro q (hq | hq)
  · have he : q = -1 := hq
    rw [he]
    norm_num
  · exact hq.1.2

theorem le_edSupValue_of_mem (S : Set (UnitBall C(K, ℝ))) (t : K) (q : ℝ)
    (hq : q ∈ Icc (-1) 1) (ht : t ∈ edCut S q) : q ≤ edSupValue S t :=
  le_csSup (edSupValues_bddAbove S t) (Or.inr ⟨hq, ht⟩)

theorem edSupValue_le_of_not_mem (S : Set (UnitBall C(K, ℝ))) (t : K) (q : ℝ)
    (hq : -1 ≤ q) (ht : t ∉ edCut S q) : edSupValue S t ≤ q := by
  apply csSup_le (edSupValues_nonempty S t)
  rintro r (hr | hr)
  · have he : r = -1 := hr
    simpa only [he] using hq
  · by_contra h
    exact ht (edCut_antitone S (le_of_not_ge h) hr.2)

theorem exists_cut_above_of_lt (S : Set (UnitBall C(K, ℝ))) (t : K) (a : ℝ)
    (ha : -1 ≤ a) (ht : a < edSupValue S t) :
    ∃ q, q ∈ Icc (-1) 1 ∧ a < q ∧ t ∈ edCut S q := by
  by_contra hn
  apply not_le_of_gt ht
  apply csSup_le (edSupValues_nonempty S t)
  rintro q (hq | hq)
  · have he : q = -1 := hq
    simpa only [he] using ha
  · by_contra h
    exact hn ⟨q, hq.1, lt_of_not_ge h, hq.2⟩

theorem edSupValue_continuous (S : Set (UnitBall C(K, ℝ))) : Continuous (edSupValue S) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change a < edSupValue S t at ht
    by_cases ha : a < -1
    · apply Filter.mem_of_superset Filter.univ_mem
      intro x _
      exact ha.trans_le (edSupValue_bounds S x).1
    · obtain ⟨q, hq, haq, htq⟩ := exists_cut_above_of_lt S t a (le_of_not_gt ha) ht
      apply Filter.mem_of_superset ((edCut_isClopen S q).isOpen.mem_nhds htq)
      intro x hx
      exact haq.trans_le (le_edSupValue_of_mem S x q hq hx)
  · apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change edSupValue S t < a at ht
    by_cases ha : 1 < a
    · apply Filter.mem_of_superset Filter.univ_mem
      intro x _
      exact (edSupValue_bounds S x).2.trans_lt ha
    · obtain ⟨q, hqt, hqa⟩ := exists_between ht
      have hq₀ : -1 ≤ q := (edSupValue_bounds S t).1.trans hqt.le
      have hq₁ : q ≤ 1 := hqa.le.trans (le_of_not_gt ha)
      have htq : t ∉ edCut S q := fun h =>
        (not_le_of_gt hqt) (le_edSupValue_of_mem S t q ⟨hq₀, hq₁⟩ h)
      apply Filter.mem_of_superset ((edCut_isClopen S q).isClosed.isOpen_compl.mem_nhds htq)
      intro x hx
      exact (edSupValue_le_of_not_mem S x q hq₀ hx).trans_lt hqa

noncomputable def edSup (S : Set (UnitBall C(K, ℝ))) : UnitBall C(K, ℝ) :=
  ⟨⟨edSupValue S, edSupValue_continuous S⟩,
    (ContinuousMap.norm_le _ (by norm_num)).mpr (fun t => abs_le.mpr (edSupValue_bounds S t))⟩

theorem edSup_upper (S : Set (UnitBall C(K, ℝ))) (f : UnitBall C(K, ℝ)) (hf : f ∈ S)
    (t : K) : f.val t ≤ (edSup S).val t := by
  change f.val t ≤ edSupValue S t
  by_contra hn
  obtain ⟨q, hqg, hqf⟩ := exists_between (lt_of_not_ge hn)
  have hq : q ∈ Icc (-1) 1 :=
    ⟨(edSupValue_bounds S t).1.trans hqg.le, hqf.le.trans (continuousBall_bounds f t).2⟩
  have htq : t ∈ edCut S q := subset_closure (mem_iUnion.mpr ⟨⟨f, hf⟩, hqf⟩)
  exact (not_le_of_gt hqg) (le_edSupValue_of_mem S t q hq htq)

theorem edSup_le (S : Set (UnitBall C(K, ℝ))) (h : UnitBall C(K, ℝ))
    (hh : ∀ f ∈ S, ∀ t, f.val t ≤ h.val t) (t : K) : (edSup S).val t ≤ h.val t := by
  change edSupValue S t ≤ h.val t
  apply csSup_le (edSupValues_nonempty S t)
  rintro q (hq | hq)
  · have he : q = -1 := hq
    simpa only [he] using (continuousBall_bounds h t).1
  · have hcut : edCut S q ⊆ {x | q ≤ h.val x} := by
      apply closure_minimal
      · intro x hx
        obtain ⟨f, hf⟩ := mem_iUnion.mp hx
        exact hf.le.trans (hh f.val f.property x)
      · exact isClosed_le continuous_const h.val.continuous
    exact hcut hq.2

theorem edSup_isLUB (S : Set (UnitBall C(K, ℝ))) : IsLUB S (edSup S) := by
  refine ⟨fun f hf t => edSup_upper S f hf t, ?_⟩
  intro h hh t
  exact edSup_le S h (fun f hf t => hh hf t) t

@[instance_reducible] noncomputable def edBallCompleteLattice : CompleteLattice (UnitBall C(K, ℝ)) := by
  letI : SupSet (UnitBall C(K, ℝ)) := ⟨edSup⟩
  exact completeLatticeOfSup _ edSup_isLUB

end BFPP
