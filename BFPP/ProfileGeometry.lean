import BFPP.Profiles
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Ring

/-! # Closedness and convexity of the increasing-profile domain -/

namespace BFPP

set_option autoImplicit false

open Set

universe u
variable {ι : Type u} [LinearOrder ι] [OrderBot ι]

private theorem isClosed_forall {X : Type*} {J : Sort*} [TopologicalSpace X]
    {p : J → X → Prop} (h : ∀ j, IsClosed {x | p j x}) :
    IsClosed {x | ∀ j, p j x} := by
  simpa only [Set.ofPred_forall] using isClosed_iInter h

theorem profileSet_isClosed : IsClosed (profileSet ι) := by
  have heval (i : ι) : Continuous (fun f : BoundedFamily ι => f i) :=
    (BoundedFamily.evaluation_nonexpansive i).continuous
  have hmono : IsClosed {f : BoundedFamily ι | Monotone f} :=
    isClosed_forall fun i => isClosed_forall fun j =>
      isClosed_forall fun (_h : i ≤ j) => isClosed_le (heval i) (heval j)
  exact (isClosed_eq (heval ⊥) continuous_const).inter
    (hmono.inter (isClosed_forall fun i => isClosed_Icc.preimage (heval i)))

theorem profileSet_convex : Convex ℝ (profileSet ι) := by
  intro x hx y hy r s hr hs hrs
  change (r * x ⊥ + s * y ⊥ = 0) ∧
    Monotone (fun i => r * x i + s * y i) ∧
    ∀ i, r * x i + s * y i ∈ Icc (0 : ℝ) 2
  refine ⟨?_, ?_, ?_⟩
  · rw [hx.1, hy.1]
    ring
  · intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2.1 hij) hr)
      (mul_le_mul_of_nonneg_left (hy.2.1 hij) hs)
  · intro i
    constructor
    · exact add_nonneg (mul_nonneg hr (hx.2.2 i).1) (mul_nonneg hs (hy.2.2 i).1)
    · have h₁ := mul_le_mul_of_nonneg_left (hx.2.2 i).2 hr
      have h₂ := mul_le_mul_of_nonneg_left (hy.2.2 i).2 hs
      linarith

theorem Profile.norm_le_two (a : Profile ι) : ‖a.val‖ ≤ 2 := by
  letI : TopologicalSpace ι := ⊥
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 2)).2
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (a.nonneg i)]
  exact a.le_two i

noncomputable def Profile.mix (a b : Profile ι) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) : Profile ι :=
  ⟨r • a.val + s • b.val, profileSet_convex a.property b.property hr hs hrs⟩

@[simp] theorem Profile.mix_apply (a b : Profile ι) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) (i : ι) :
    (a.mix b r s hr hs hrs).val i = r * a.val i + s * b.val i := rfl

theorem Profile.tail_mix (a b : Profile ι) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    (a.mix b r s hr hs hrs).tail = r * a.tail + s * b.tail := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    exact add_le_add (mul_le_mul_of_nonneg_left (a.le_tail i) hr)
      (mul_le_mul_of_nonneg_left (b.le_tail i) hs)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup
      (show a.tail - ε < ⨆ i, a.val i by change a.tail - ε < a.tail; linarith)
    obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup
      (show b.tail - ε < ⨆ j, b.val j by change b.tail - ε < b.tail; linarith)
    have ha : a.tail - ε ≤ a.val (max i j) :=
      hi.le.trans (a.monotone (le_max_left i j))
    have hb : b.tail - ε ≤ b.val (max i j) :=
      hj.le.trans (b.monotone (le_max_right i j))
    have h₁ := mul_le_mul_of_nonneg_left ha hr
    have h₂ := mul_le_mul_of_nonneg_left hb hs
    have h₃ := (a.mix b r s hr hs hrs).le_tail (max i j)
    rw [Profile.mix_apply] at h₃
    have hεsum : (r + s) * ε = ε := by rw [hrs, one_mul]
    nlinarith

/-- A concrete profile used to witness nonemptiness of the coefficient domain. -/
noncomputable def Profile.stepOne : Profile ι := by
  classical
  let f : BoundedFamily ι := BoundedFamily.ofBound
    (fun i => if i = ⊥ then 0 else 1) 1 (fun i => by split_ifs <;> norm_num)
  refine ⟨f, ?_, ?_, ?_⟩
  · simp [f]
  · intro i j hij
    change (if i = ⊥ then (0 : ℝ) else 1) ≤ (if j = ⊥ then 0 else 1)
    by_cases hi : i = ⊥
    · rw [if_pos hi]
      split_ifs <;> norm_num
    · have hj : j ≠ ⊥ := fun h => hi (bot_unique (h ▸ hij))
      simp [hi, hj]
  · intro i
    change (if i = ⊥ then (0 : ℝ) else 1) ∈ Icc 0 2
    split_ifs <;> norm_num

theorem Profile.tail_stepOne [NoMaxOrder ι] : (Profile.stepOne : Profile ι).tail = 1 := by
  classical
  apply le_antisymm
  · apply ciSup_le
    intro i
    change (if i = ⊥ then (0 : ℝ) else 1) ≤ 1
    split_ifs <;> norm_num
  · obtain ⟨i, hi⟩ := exists_gt (⊥ : ι)
    have h := (Profile.stepOne : Profile ι).le_tail i
    change (if i = ⊥ then (0 : ℝ) else 1) ≤ _ at h
    simpa [ne_of_gt hi] using h

end BFPP
