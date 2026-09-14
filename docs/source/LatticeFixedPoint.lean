import BFPP.InvariantIntervals
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-! # A fixed point theorem for complete lattices with interval metric balls -/

namespace BFPP

set_option autoImplicit false
open Set

variable {A : Type*} [MetricSpace A] [CompleteLattice A]

theorem fixedPoint_of_interval_balls
    (hballs : ∀ x : A, ∀ r : ℝ, 0 ≤ r → ∃ a b, Metric.closedBall x r = Icc a b)
    (hmid : ∀ l u : A, l ≤ u → ∃ m ∈ Icc l u, ∀ z ∈ Icc l u, dist m z ≤ dist l u / 2)
    (T : A → A) (hLip : LipschitzWith 1 T) : ∃ x, T x = x := by
  classical
  obtain ⟨l, u, hlu, hT, hmin⟩ := exists_minimal_invariant_interval T
  let M := Icc l u
  let r := dist l u / 2
  have hr : 0 ≤ r := div_nonneg dist_nonneg (by norm_num)
  let N : Set A := {x | x ∈ M ∧ ∀ y ∈ M, dist x y ≤ r}
  obtain ⟨m, hmM, hm⟩ := hmid l u hlu
  have hmN : m ∈ N := ⟨hmM, hm⟩
  choose a b hab using fun y : M => hballs y.val r hr
  let L := l ⊔ ⨆ y : M, a y
  let U := u ⊓ ⨅ y : M, b y
  have hN : N = Icc L U := by
    ext x
    constructor
    · rintro ⟨hxM, hx⟩
      have hxI : ∀ y : M, x ∈ Icc (a y) (b y) := by
        intro y
        rw [← hab y]
        exact hx y.val y.property
      exact ⟨sup_le hxM.1 (iSup_le (fun y => (hxI y).1)),
        le_inf hxM.2 (le_iInf (fun y => (hxI y).2))⟩
    · intro hx
      refine ⟨⟨le_sup_left.trans hx.1, hx.2.trans inf_le_left⟩, ?_⟩
      intro y hy
      have hxI : x ∈ Icc (a ⟨y, hy⟩) (b ⟨y, hy⟩) :=
        ⟨(le_iSup a ⟨y, hy⟩).trans (le_sup_right.trans hx.1),
          (hx.2.trans inf_le_right).trans (iInf_le b ⟨y, hy⟩)⟩
      rw [← hab ⟨y, hy⟩] at hxI
      exact hxI
  have hLU : L ≤ U := by
    have hmI := hN ▸ hmN
    exact hmI.1.trans hmI.2
  have hNT : MapsTo T N N := by
    intro x hx
    have hTx : T x ∈ M := hT hx.1
    refine ⟨hTx, ?_⟩
    obtain ⟨a', b', hball⟩ := hballs (T x) r hr
    let p := l ⊔ a'
    let q := u ⊓ b'
    have hsub : Icc p q ⊆ M := fun z hz =>
      ⟨le_sup_left.trans hz.1, hz.2.trans inf_le_left⟩
    have hself : T x ∈ Icc a' b' := by
      rw [← hball]
      simpa using hr
    have hTxI : T x ∈ Icc p q :=
      ⟨sup_le hTx.1 hself.1, le_inf hTx.2 hself.2⟩
    have hpq : p ≤ q := hTxI.1.trans hTxI.2
    have hinv : MapsTo T (Icc p q) (Icc p q) := by
      intro z hz
      have hzM := hsub hz
      have hTz := hT hzM
      have hd : dist (T z) (T x) ≤ r := by
        have hdist : dist (T z) (T x) ≤ dist z x := by
          simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul z x
        exact hdist.trans (by simpa only [dist_comm] using hx.2 z hzM)
      have hTzI : T z ∈ Icc a' b' := by
        rw [← hball]
        exact hd
      exact ⟨sup_le hTz.1 hTzI.1, le_inf hTz.2 hTzI.2⟩
    have hMsub := hmin p q hpq hsub hinv
    intro y hy
    have hyI := hMsub hy
    have hyab : y ∈ Icc a' b' :=
      ⟨le_sup_right.trans hyI.1, hyI.2.trans inf_le_right⟩
    rw [← hball] at hyab
    simpa only [Metric.mem_closedBall, dist_comm] using hyab
  have hNM : Icc L U ⊆ Icc l u := by
    rw [← hN]
    exact fun x hx => hx.1
  have hTN : MapsTo T (Icc L U) (Icc L U) := hN ▸ hNT
  have hMN : M ⊆ N := by
    rw [hN]
    exact hmin L U hLU hNM hTN
  have hlN := hMN (show l ∈ M from ⟨le_rfl, hlu⟩)
  have hdiam := hlN.2 u (show u ∈ M from ⟨hlu, le_rfl⟩)
  have heq : l = u := by
    apply dist_eq_zero.mp
    dsimp [r] at hdiam
    linarith [dist_nonneg (x := l) (y := u)]
  refine ⟨l, ?_⟩
  have hTl := hT (show l ∈ Icc l u from ⟨le_rfl, hlu⟩)
  rw [← heq] at hTl
  exact le_antisymm hTl.2 hTl.1

end BFPP
