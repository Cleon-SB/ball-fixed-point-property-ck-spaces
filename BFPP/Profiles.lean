import BFPP.BoundedFamilies
import Mathlib.Order.WellFounded
import Mathlib.Analysis.Convex.Basic

/-!
# Increasing profiles and transfinite delay

The index is any linear order with a least element. `delayValue` is uniformly
the supremum over strict predecessors, except at the least element. On ordinal
indices this is the successor--limit formula of the paper.
-/

namespace BFPP

set_option autoImplicit false

open Set

universe u
variable {ι : Type u} [LinearOrder ι] [OrderBot ι]

def profileSet (ι : Type u) [LinearOrder ι] [OrderBot ι] : Set (BoundedFamily ι) :=
  {a | a ⊥ = 0 ∧ Monotone a ∧ ∀ i, a i ∈ Icc (0 : ℝ) 2}

abbrev Profile (ι : Type u) [LinearOrder ι] [OrderBot ι] :=
  {a : BoundedFamily ι // a ∈ profileSet ι}

namespace Profile

theorem at_bot (a : Profile ι) : a.val ⊥ = 0 := a.property.1
theorem monotone (a : Profile ι) : Monotone a.val := a.property.2.1
theorem nonneg (a : Profile ι) (i : ι) : 0 ≤ a.val i := (a.property.2.2 i).1
theorem le_two (a : Profile ι) (i : ι) : a.val i ≤ 2 := (a.property.2.2 i).2

noncomputable def tail (a : Profile ι) : ℝ := BoundedFamily.supremum a.val

theorem le_tail (a : Profile ι) (i : ι) : a.val i ≤ a.tail :=
  le_ciSup a.val.bddAbove_range i

theorem tail_nonneg (a : Profile ι) : 0 ≤ a.tail :=
  (a.nonneg ⊥).trans (a.le_tail ⊥)

theorem tail_le_two (a : Profile ι) : a.tail ≤ 2 := ciSup_le a.le_two

theorem tail_nonexpansive : LipschitzWith 1 (tail : Profile ι → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  exact BoundedFamily.supremum_nonexpansive.dist_le_mul a.val b.val

noncomputable def delayValue (a : Profile ι) (i : ι) : ℝ := by
  classical
  exact if i = ⊥ then 0 else ⨆ j : Iio i, a.val j.val

@[simp] theorem delayValue_bot (a : Profile ι) : a.delayValue ⊥ = 0 := by
  simp [delayValue]

theorem prefix_bddAbove (a : Profile ι) (i : ι) :
    BddAbove (range (fun j : Iio i => a.val j.val)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact a.le_two j.val

theorem delayValue_nonneg (a : Profile ι) (i : ι) : 0 ≤ a.delayValue i := by
  classical
  by_cases hi : i = ⊥
  · simp [delayValue, hi]
  · rw [delayValue, if_neg hi]
    have hbot : (⊥ : ι) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
    exact (a.nonneg ⊥).trans (le_ciSup (a.prefix_bddAbove i) ⟨⊥, hbot⟩)

theorem delayValue_le_apply (a : Profile ι) (i : ι) : a.delayValue i ≤ a.val i := by
  classical
  by_cases hi : i = ⊥
  · simp [hi, a.at_bot]
  · rw [delayValue, if_neg hi]
    have hbot : (⊥ : ι) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
    letI : Nonempty (Iio i) := ⟨⟨⊥, hbot⟩⟩
    exact ciSup_le (fun j => a.monotone j.property.le)

theorem delayValue_le_two (a : Profile ι) (i : ι) : a.delayValue i ≤ 2 :=
  (a.delayValue_le_apply i).trans (a.le_two i)

theorem delayValue_monotone (a : Profile ι) : Monotone a.delayValue := by
  classical
  intro i j hij
  by_cases hi : i = ⊥
  · simpa [hi] using a.delayValue_nonneg j
  have hj : j ≠ ⊥ := by
    intro h
    exact hi (bot_unique (h ▸ hij))
  have hbot : (⊥ : ι) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
  letI : Nonempty (Iio i) := ⟨⟨⊥, hbot⟩⟩
  rw [delayValue, if_neg hi, delayValue, if_neg hj]
  apply ciSup_le
  intro k
  exact le_ciSup (a.prefix_bddAbove j) ⟨k.val, lt_of_lt_of_le k.property hij⟩

noncomputable def delay (a : Profile ι) : Profile ι := by
  let f : BoundedFamily ι := BoundedFamily.ofBound a.delayValue 2 (fun i => by
    rw [Real.norm_eq_abs, abs_of_nonneg (a.delayValue_nonneg i)]
    exact a.delayValue_le_two i)
  exact ⟨f, a.delayValue_bot, a.delayValue_monotone,
    fun i => ⟨a.delayValue_nonneg i, a.delayValue_le_two i⟩⟩

@[simp] theorem delay_apply (a : Profile ι) (i : ι) : a.delay.val i = a.delayValue i := rfl

theorem delay_le (a : Profile ι) : a.delay ≤ a := a.delayValue_le_apply

theorem delay_nonexpansive : LipschitzWith 1 (delay : Profile ι → Profile ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  change dist a.delay.val b.delay.val ≤ dist a b
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).2
  intro i
  classical
  by_cases hi : i = ⊥
  · simpa [hi] using (dist_nonneg : 0 ≤ dist a b)
  · have hbot : (⊥ : ι) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
    letI : Nonempty (Iio i) := ⟨⟨⊥, hbot⟩⟩
    simp only [delay_apply, delayValue, if_neg hi]
    apply abs_ciSup_sub_ciSup_le _ _ (a.prefix_bddAbove i) (b.prefix_bddAbove i)
    intro j
    exact BoundedFamily.abs_sub_apply_le_dist a.val b.val j.val

theorem subsolution_eq_zero [WellFoundedLT ι] (a : Profile ι) (h : a ≤ a.delay) :
    ∀ i, a.val i = 0 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    classical
    by_cases hi : i = ⊥
    · simpa [hi] using a.at_bot
    have hbot : (⊥ : ι) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
    letI : Nonempty (Iio i) := ⟨⟨⊥, hbot⟩⟩
    have hz : a.delayValue i = 0 := by
      simp only [delayValue, if_neg hi]
      have hfun : (fun j : Iio i => a.val j.val) = (fun _ : Iio i => (0 : ℝ)) :=
        funext (fun j => ih j.val j.property)
      rw [hfun, ciSup_const]
    have hle : a.val i ≤ a.delayValue i := h i
    exact le_antisymm (hz ▸ hle) (a.nonneg i)

theorem tail_delay [NoMaxOrder ι] (a : Profile ι) : a.delay.tail = a.tail := by
  classical
  apply le_antisymm
  · apply ciSup_le
    intro i
    exact (a.delayValue_le_apply i).trans (a.le_tail i)
  · apply ciSup_le
    intro i
    obtain ⟨j, hij⟩ := exists_gt i
    have hj : j ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hij)
    calc
      a.val i ≤ a.delay.val j := by
        simp only [delay_apply, delayValue, if_neg hj]
        exact le_ciSup (a.prefix_bddAbove j) ⟨i, hij⟩
      _ ≤ a.delay.tail := a.delay.le_tail j

end Profile
end BFPP
