import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The finite positive-synthesis estimate

For an increasing sequence of weights in `[0,W]`, bounds on every tail sum of
the coefficients give the same bounds, scaled by `W`, on the weighted sum.
This is the finite estimate behind the positive operator extension.
-/

namespace BFPP

set_option autoImplicit false

universe u
variable {ι : Type u}

def TailSumBounds (l : List ι) (c : ι → ℝ) (m M : ℝ) : Prop :=
  ∀ t : List ι, t <:+ l → m ≤ (t.map c).sum ∧ (t.map c).sum ≤ M

theorem sum_shift_weights (l : List ι) (c w : ι → ℝ) (b : ℝ) :
    (l.map (fun i => c i * (w i - b))).sum =
      (l.map (fun i => c i * w i)).sum - (l.map c).sum * b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem finite_synthesis_bounds [Preorder ι] (l : List ι) (c w : ι → ℝ)
    (m M W : ℝ) (hW : 0 ≤ W) (hs : l.Pairwise (· ≤ ·))
    (hw : Monotone w) (hb : ∀ i ∈ l, 0 ≤ w i ∧ w i ≤ W)
    (ht : TailSumBounds l c m M) :
    m * W ≤ (l.map (fun i => c i * w i)).sum ∧
      (l.map (fun i => c i * w i)).sum ≤ M * W := by
  induction l generalizing w W with
  | nil =>
    have hzero := ht [] (by simp)
    simp only [List.map_nil, List.sum_nil] at hzero ⊢
    exact ⟨mul_nonpos_of_nonpos_of_nonneg hzero.1 hW, mul_nonneg hzero.2 hW⟩
  | cons a l ih =>
    have hhead := hb a (List.mem_cons_self ..)
    have hp := List.pairwise_cons.mp hs
    have htail : TailSumBounds l c m M := by
      intro t ht'
      exact ht t (ht'.trans (List.suffix_cons a l))
    have hb' : ∀ i ∈ l, 0 ≤ w i - w a ∧ w i - w a ≤ W - w a := by
      intro i hi
      have hwi := hb i (List.mem_cons_of_mem a hi)
      exact ⟨sub_nonneg.mpr (hw (hp.1 i hi)), sub_le_sub_right hwi.2 _⟩
    have hm : Monotone (fun i => w i - w a) := fun _ _ hij => sub_le_sub_right (hw hij) _
    have hi := ih (fun i => w i - w a) (W - w a) (sub_nonneg.mpr hhead.2)
      hp.2 hm hb' htail
    have hall := ht (a :: l) (by simp)
    simp only [List.map_cons, List.sum_cons] at hall ⊢
    have hlow := mul_le_mul_of_nonneg_right hall.1 hhead.1
    have hupp := mul_le_mul_of_nonneg_right hall.2 hhead.1
    rw [sum_shift_weights] at hi
    constructor <;> nlinarith [hi.1, hi.2]

theorem finite_synthesis_abs_bound [Preorder ι] (l : List ι) (c w : ι → ℝ)
    (C : ℝ) (hs : l.Pairwise (· ≤ ·)) (hw : Monotone w)
    (hb : ∀ i ∈ l, 0 ≤ w i ∧ w i ≤ 1)
    (ht : ∀ t : List ι, t <:+ l → |(t.map c).sum| ≤ C) :
    |(l.map (fun i => c i * w i)).sum| ≤ C := by
  have h := finite_synthesis_bounds l c w (-C) C 1 (by norm_num) hs hw hb
    (fun t htl => abs_le.mp (ht t htl))
  apply abs_le.mpr
  simpa only [mul_one] using h

theorem finite_synthesis_nonneg [Preorder ι] (l : List ι) (c w : ι → ℝ)
    (M : ℝ) (hs : l.Pairwise (· ≤ ·)) (hw : Monotone w)
    (hb : ∀ i ∈ l, 0 ≤ w i ∧ w i ≤ 1) (ht : TailSumBounds l c 0 M) :
    0 ≤ (l.map (fun i => c i * w i)).sum := by
  have h := (finite_synthesis_bounds l c w 0 M 1 (by norm_num) hs hw hb ht).1
  simpa only [zero_mul] using h

noncomputable def stepListValue [LinearOrder ι] (l : List ι) (c : ι → ℝ) (i : ι) : ℝ :=
  (l.map (fun j => if i ≤ j then c j else 0)).sum

theorem tailSumBounds_of_stepList [LinearOrder ι] (l : List ι) (c : ι → ℝ) (m M : ℝ)
    (hs : l.Pairwise (· < ·)) (hm : m ≤ 0) (hM : 0 ≤ M)
    (hf : ∀ i ∈ l, m ≤ stepListValue l c i ∧ stepListValue l c i ≤ M) :
    TailSumBounds l c m M := by
  induction l with
  | nil =>
    intro t ht
    have he := List.suffix_nil.mp ht
    simpa [he] using And.intro hm hM
  | cons a l ih =>
    have hp := List.pairwise_cons.mp hs
    have htail : TailSumBounds l c m M := by
      apply ih hp.2
      intro i hi
      have h := hf i (List.mem_cons_of_mem a hi)
      have hia : ¬ i ≤ a := not_le.mpr (hp.1 i hi)
      simpa [stepListValue, hia] using h
    have hfirst : stepListValue (a :: l) c a = c a + (l.map c).sum := by
      have he : l.map (fun j => if a ≤ j then c j else 0) = l.map c := by
        apply List.map_congr_left
        intro j hj
        simp only [if_pos (hp.1 j hj).le]
      simp only [stepListValue, List.map_cons, if_pos le_rfl, List.sum_cons, he]
    intro t ht
    rcases List.suffix_cons_iff.mp ht with rfl | ht
    · have h := hf a (List.mem_cons_self ..)
      simpa only [hfirst, List.map_cons, List.sum_cons] using h
    · exact htail t ht

theorem sum_map_sort [LinearOrder ι] (s : Finset ι) (f : ι → ℝ) :
    (s.sort.map f).sum = ∑ i ∈ s, f i := by
  rw [← List.sum_toFinset f (s.sort_nodup (· ≤ ·)), Finset.sort_toFinset]

noncomputable def stepFinsetValue [LinearOrder ι] (s : Finset ι) (c : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ s, if i ≤ j then c j else 0

theorem finite_synthesis_bounds_finset [LinearOrder ι] (s : Finset ι) (c w : ι → ℝ)
    (m M : ℝ) (hm : m ≤ 0) (hM : 0 ≤ M) (hw : Monotone w)
    (hb : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1)
    (hf : ∀ i, m ≤ stepFinsetValue s c i ∧ stepFinsetValue s c i ≤ M) :
    m ≤ ∑ i ∈ s, c i * w i ∧ (∑ i ∈ s, c i * w i) ≤ M := by
  have ht : TailSumBounds s.sort c m M := by
    apply tailSumBounds_of_stepList _ _ _ _ s.sortedLT_sort.pairwise hm hM
    intro i _hi
    simpa only [stepListValue, sum_map_sort, stepFinsetValue] using hf i
  have h := finite_synthesis_bounds s.sort c w m M 1 (by norm_num)
    (s.pairwise_sort (· ≤ ·)) hw
    (fun i hi => hb i (by simpa using hi)) ht
  simpa only [sum_map_sort, mul_one] using h

theorem finite_synthesis_abs_bound_finset [LinearOrder ι] (s : Finset ι) (c w : ι → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hw : Monotone w)
    (hb : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1)
    (hf : ∀ i, |stepFinsetValue s c i| ≤ C) :
    |∑ i ∈ s, c i * w i| ≤ C := by
  apply abs_le.mpr
  exact finite_synthesis_bounds_finset s c w (-C) C (neg_nonpos.mpr hC) hC hw hb
    (fun i => abs_le.mp (hf i))

end BFPP
