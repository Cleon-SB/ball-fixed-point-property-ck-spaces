import BFPP.OrdinalIndex
import Mathlib.SetTheory.Ordinal.Principal

/-! # Pairing coordinates below a limit ordinal -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u

theorem ordinal_two_mul_limit (tau : Ordinal.{u}) (htau : IsSuccLimit tau) : 2 * tau = tau :=
  Ordinal.mul_omega0_dvd (by norm_num) (by simpa using Ordinal.natCast_lt_omega0 2)
    (Ordinal.isSuccPrelimit_iff_omega0_dvd.mp htau.isSuccPrelimit)

theorem ordinal_mod_two_cases (a : Ordinal.{u}) : a % 2 = 0 ∨ a % 2 = 1 := by
  have h := Ordinal.mod_lt a (by norm_num : (2 : Ordinal.{u}) ≠ 0)
  have hle : a % 2 ≤ 1 := Order.le_of_lt_succ (by simpa using h)
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl (Order.lt_one_iff.mp hlt)
  · exact Or.inr heq

variable (κ : Ordinal.{u}) [hκ : Fact (IsSuccLimit κ)]

noncomputable def evenIndex (i : OrdinalIndex κ) : OrdinalIndex κ :=
  ⟨2 * i.val, by
    have h : 2 * i.val < 2 * κ :=
      (Ordinal.isNormal_mul_right (by norm_num : (0 : Ordinal.{u}) < 2)).strictMono i.property
    exact h.trans_eq (ordinal_two_mul_limit κ hκ.out)⟩

noncomputable def oddIndex (i : OrdinalIndex κ) : OrdinalIndex κ :=
  ⟨2 * i.val + 1, hκ.out.succ_lt (evenIndex κ i).property⟩

noncomputable def halfIndex (i : OrdinalIndex κ) : OrdinalIndex κ :=
  ⟨i.val / 2, (Ordinal.lt_mul_iff_div_lt (by norm_num : (2 : Ordinal.{u}) ≠ 0)).mp
    (by rw [ordinal_two_mul_limit κ hκ.out]; exact i.property)⟩

@[simp] theorem half_evenIndex (i : OrdinalIndex κ) : halfIndex κ (evenIndex κ i) = i := by
  apply Subtype.ext
  exact Ordinal.mul_div_cancel i.val (by norm_num)

@[simp] theorem half_oddIndex (i : OrdinalIndex κ) : halfIndex κ (oddIndex κ i) = i := by
  apply Subtype.ext
  change (2 * i.val + 1) / 2 = i.val
  rw [Ordinal.mul_add_div i.val (by norm_num)]
  norm_num [Ordinal.div_eq_zero_of_lt]

@[simp] theorem evenIndex_mod (i : OrdinalIndex κ) : (evenIndex κ i).val % 2 = 0 :=
  Ordinal.mul_mod _ _

@[simp] theorem oddIndex_mod (i : OrdinalIndex κ) : (oddIndex κ i).val % 2 = 1 := by
  change (2 * i.val + 1) % 2 = 1
  rw [Ordinal.mul_add_mod_self]
  exact Ordinal.mod_eq_of_lt (by norm_num)

theorem index_eq_even_or_odd (i : OrdinalIndex κ) :
    i = evenIndex κ (halfIndex κ i) ∨ i = oddIndex κ (halfIndex κ i) := by
  rcases ordinal_mod_two_cases i.val with h | h
  · left
    apply Subtype.ext
    change i.val = 2 * (i.val / 2)
    simpa only [h, add_zero] using (Ordinal.div_add_mod i.val 2).symm
  · right
    apply Subtype.ext
    change i.val = 2 * (i.val / 2) + 1
    simpa only [h] using (Ordinal.div_add_mod i.val 2).symm

@[simp] theorem evenIndex_bot : evenIndex κ ⊥ = ⊥ := by
  apply Subtype.ext
  change (2 : Ordinal.{u}) * 0 = 0
  simp

theorem evenIndex_strictMono : StrictMono (evenIndex κ) := by
  intro i j hij
  exact (Ordinal.isNormal_mul_right (by norm_num : (0 : Ordinal.{u}) < 2)).strictMono hij

theorem oddIndex_strictMono : StrictMono (oddIndex κ) := by
  intro i j hij
  change 2 * i.val + 1 < 2 * j.val + 1
  exact Order.succ_lt_succ (show 2 * i.val < 2 * j.val from evenIndex_strictMono κ hij)

end BFPP
