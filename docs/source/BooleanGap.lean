import BFPP.ChainCompleteness
import Mathlib.Order.BooleanAlgebra.Basic

/-! # A gap in a maximal chain -/

namespace BFPP

set_option autoImplicit false
open Set

variable (B : Type*) [Lattice B] [BoundedOrder B]

/-- The order-theoretic gap before selecting cofinal ordinal sequences. -/
structure ChainGap where
  lower : Set B
  upper : Set B
  lower_chain : IsChain (· ≤ ·) lower
  upper_chain : IsChain (· ≤ ·) upper
  bot_mem : ⊥ ∈ lower
  top_mem : ⊤ ∈ upper
  cross : ∀ y ∈ lower, ∀ z ∈ upper, y ≤ z
  lower_no_max : ∀ y ∈ lower, ∃ y' ∈ lower, y < y'
  upper_no_min : ∀ z ∈ upper, ∃ z' ∈ upper, z' < z
  no_interpolant : ¬ ∃ b, (∀ y ∈ lower, y ≤ b) ∧ ∀ z ∈ upper, b ≤ z

variable {B}

theorem exists_chainGap (h : ∃ s : Set B, ¬ ∃ b, IsLUB s b) : Nonempty (ChainGap B) := by
  classical
  obtain ⟨c, hc, hn⟩ := exists_chain_without_isLUB h
  obtain ⟨M', hM', hcM⟩ := hc.exists_maxChain
  let M : Flag B := Flag.ofIsMaxChain M' hM'
  let Y : Set B := {y | y ∈ M ∧ ∃ a ∈ c, y ≤ a}
  let Z : Set B := {z | z ∈ M ∧ z ∉ Y}
  have hcY : c ⊆ Y := fun a ha => ⟨hcM ha, a, ha, le_rfl⟩
  have hnotub : ∀ y ∈ Y, y ∉ upperBounds c := by
    rintro y ⟨hyM, a, ha, hya⟩ hy
    apply hn
    exact ⟨y, hy, fun b hb => hya.trans (hb ha)⟩
  have hcross : ∀ y ∈ Y, ∀ z ∈ Z, y ≤ z := by
    rintro y ⟨hyM, a, ha, hya⟩ z ⟨hzM, hzY⟩
    rcases M.le_or_le hyM hzM with hyz | hzy
    · exact hyz
    · exact (hzY ⟨hzM, a, ha, hzy.trans hya⟩).elim
  have hYmax : ∀ y ∈ Y, ∃ y' ∈ Y, y < y' := by
    intro y hy
    have hbad := hnotub y hy
    change ¬ (∀ ⦃a⦄, a ∈ c → a ≤ y) at hbad
    push Not at hbad
    obtain ⟨a, ha, hay⟩ := hbad
    refine ⟨a, hcY ha, ?_⟩
    exact lt_of_le_not_ge ((M.le_or_le hy.1 (hcM ha)).resolve_right hay) hay
  have hZmin : ∀ z ∈ Z, ∃ z' ∈ Z, z' < z := by
    intro z hz
    by_contra hnone
    have hleast : ∀ z' ∈ Z, z ≤ z' := by
      intro z' hz'
      rcases M.le_or_le hz.1 hz'.1 with hzz | hzz
      · exact hzz
      · by_contra h
        exact hnone ⟨z', hz', lt_of_le_not_ge hzz h⟩
    have hzupper : z ∈ upperBounds c := fun a ha => hcross a (hcY ha) z hz
    apply hn
    refine ⟨z, hzupper, ?_⟩
    intro b hb
    have hmeetM : z ⊓ b ∈ M := by
      apply Flag.mem_iff_forall_le_or_ge.mpr
      intro m hm
      by_cases hmY : m ∈ Y
      · right
        obtain ⟨a, ha, hma⟩ := hmY.2
        exact le_inf (hcross m hmY z hz) (hma.trans (hb ha))
      · exact Or.inl (inf_le_left.trans (hleast m ⟨hm, hmY⟩))
    have hmeetub : z ⊓ b ∈ upperBounds c := fun a ha => le_inf (hzupper ha) (hb ha)
    have hmeetZ : z ⊓ b ∈ Z := ⟨hmeetM, fun hY => hnotub _ hY hmeetub⟩
    exact (hleast _ hmeetZ).trans inf_le_right
  have hcne : c.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he] at hn
    exact hn ⟨⊥, isLUB_empty⟩
  refine ⟨{
    lower := Y
    upper := Z
    lower_chain := M.chain_le.mono (fun _ h => h.1)
    upper_chain := M.chain_le.mono (fun _ h => h.1)
    bot_mem := ?_
    top_mem := ?_
    cross := hcross
    lower_no_max := hYmax
    upper_no_min := hZmin
    no_interpolant := ?_ }⟩
  · obtain ⟨a, ha⟩ := hcne
    exact ⟨M.bot_mem, a, ha, bot_le⟩
  · exact ⟨M.top_mem, fun ht => hnotub ⊤ ht (fun _ _ => le_top)⟩
  · rintro ⟨b, hYb, hbZ⟩
    have hbM : b ∈ M := by
      apply Flag.mem_iff_forall_le_or_ge.mpr
      intro m hm
      by_cases hmY : m ∈ Y
      · exact Or.inr (hYb m hmY)
      · exact Or.inl (hbZ m ⟨hm, hmY⟩)
    by_cases hbY : b ∈ Y
    · obtain ⟨b', hb', hlt⟩ := hYmax b hbY
      exact (not_le_of_gt hlt) (hYb b' hb')
    · obtain ⟨b', hb', hlt⟩ := hZmin b ⟨hbM, hbY⟩
      exact (not_le_of_gt hlt) (hbZ b' hb')

end BFPP
