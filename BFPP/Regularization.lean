import BFPP.Profiles
import Mathlib.Topology.Order.SuccPred

/-! # Successor--limit formulas and continuous regularization -/

namespace BFPP

set_option autoImplicit false

open Set Order Filter Topology

universe u
variable {ι : Type u} [LinearOrder ι] [OrderBot ι]

namespace Profile

theorem delayValue_succ [SuccOrder ι] [NoMaxOrder ι] (a : Profile ι) (i : ι) :
    a.delayValue (Order.succ i) = a.val i := by
  classical
  have hne : Order.succ i ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le (Order.lt_succ i))
  rw [delayValue, if_neg hne]
  letI : Nonempty (Iio (Order.succ i)) := ⟨⟨i, Order.lt_succ i⟩⟩
  apply le_antisymm
  · exact ciSup_le (fun j => a.monotone (Order.lt_succ_iff.mp j.property))
  · exact le_ciSup (a.prefix_bddAbove _) ⟨i, Order.lt_succ i⟩

noncomputable def regularizeValue (a : Profile ι) (i : ι) : ℝ := by
  classical
  exact if IsSuccLimit i then a.delayValue i else a.val i

theorem regularizeValue_nonneg (a : Profile ι) (i : ι) : 0 ≤ a.regularizeValue i := by
  classical
  unfold regularizeValue
  split_ifs
  · exact a.delayValue_nonneg i
  · exact a.nonneg i

theorem regularizeValue_le_apply (a : Profile ι) (i : ι) : a.regularizeValue i ≤ a.val i := by
  classical
  unfold regularizeValue
  split_ifs
  · exact a.delayValue_le_apply i
  · exact le_rfl

theorem delayValue_le_regularizeValue (a : Profile ι) (i : ι) :
    a.delayValue i ≤ a.regularizeValue i := by
  classical
  unfold regularizeValue
  split_ifs
  · exact le_rfl
  · exact a.delayValue_le_apply i

@[simp] theorem regularizeValue_bot (a : Profile ι) : a.regularizeValue ⊥ = 0 := by
  simp [regularizeValue, not_isSuccLimit_bot, a.at_bot]

@[simp] theorem regularizeValue_succ [SuccOrder ι] [NoMaxOrder ι] (a : Profile ι) (i : ι) :
    a.regularizeValue (Order.succ i) = a.val (Order.succ i) := by
  simp [regularizeValue, not_isSuccLimit_succ]

theorem regularizeValue_limit (a : Profile ι) (i : ι) (hi : IsSuccLimit i) :
    a.regularizeValue i = ⨆ j : Iio i, a.val j.val := by
  simp [regularizeValue, hi, delayValue, hi.ne_bot]

theorem regularizeValue_monotone (a : Profile ι) : Monotone a.regularizeValue := by
  classical
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  by_cases hj : IsSuccLimit j
  · rw [regularizeValue_limit a j hj]
    exact (a.regularizeValue_le_apply i).trans (le_ciSup (a.prefix_bddAbove j) ⟨i, hij⟩)
  · have he : a.regularizeValue j = a.val j := by simp [regularizeValue, hj]
    rw [he]
    exact (a.regularizeValue_le_apply i).trans (a.monotone hij.le)

noncomputable def regularize (a : Profile ι) : Profile ι := by
  let f : BoundedFamily ι := BoundedFamily.ofBound a.regularizeValue 2 (fun i => by
    rw [Real.norm_eq_abs, abs_of_nonneg (a.regularizeValue_nonneg i)]
    exact (a.regularizeValue_le_apply i).trans (a.le_two i))
  exact ⟨f, a.regularizeValue_bot, a.regularizeValue_monotone,
    fun i => ⟨a.regularizeValue_nonneg i,
      (a.regularizeValue_le_apply i).trans (a.le_two i)⟩⟩

@[simp] theorem regularize_apply (a : Profile ι) (i : ι) :
    a.regularize.val i = a.regularizeValue i := rfl

theorem regularize_le (a : Profile ι) : a.regularize ≤ a := a.regularizeValue_le_apply

theorem regularize_nonexpansive : LipschitzWith 1 (regularize : Profile ι → Profile ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  change dist a.regularize.val b.regularize.val ≤ dist a b
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).2
  intro i
  classical
  by_cases hi : IsSuccLimit i
  · simp only [regularize_apply, regularizeValue, if_pos hi]
    have h := delay_nonexpansive.dist_le_mul a b
    have hd : |a.delayValue i - b.delayValue i| ≤ dist a.delay b.delay :=
      BoundedFamily.abs_sub_apply_le_dist a.delay.val b.delay.val i
    exact hd.trans (by simpa only [NNReal.coe_one, one_mul] using h)
  · simp only [regularize_apply, regularizeValue, if_neg hi]
    exact BoundedFamily.abs_sub_apply_le_dist a.val b.val i

theorem tail_regularize [NoMaxOrder ι] (a : Profile ι) : a.regularize.tail = a.tail := by
  apply le_antisymm
  · exact ciSup_le (fun i => (a.regularizeValue_le_apply i).trans (a.le_tail i))
  · rw [← a.tail_delay]
    exact ciSup_le (fun i => (a.delayValue_le_regularizeValue i).trans (a.regularize.le_tail i))

/-- Regularization is continuous for the actual order topology, not the discrete
topology used to present the ambient space of bounded families. -/
theorem regularizeValue_continuous [SuccOrder ι] [NoMaxOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] (a : Profile ι) : Continuous a.regularizeValue := by
  apply continuous_iff_continuousAt.mpr
  intro i
  by_cases hi : IsSuccLimit i
  · apply Metric.continuousAt_iff'.mpr
    intro ε hε
    letI : Nonempty (Iio i) := hi.nonempty_Iio.to_subtype
    have happrox : a.regularizeValue i - ε < ⨆ j : Iio i, a.val j.val := by
      rw [← regularizeValue_limit a i hi]
      linarith
    obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup happrox
    have hs : Order.succ j.val < i := hi.succ_lt j.property
    have hn : Ioo (Order.succ j.val) (Order.succ i) ∈ 𝓝 i :=
      isOpen_Ioo.mem_nhds ⟨hs, Order.lt_succ i⟩
    filter_upwards [hn] with k hk
    have hki : k ≤ i := Order.lt_succ_iff.mp hk.2
    have hupper := a.regularizeValue_monotone hki
    have hlower : a.val j.val ≤ a.regularizeValue k := by
      calc
        a.val j.val ≤ a.val (Order.succ j.val) := a.monotone (Order.le_succ _)
        _ = a.regularizeValue (Order.succ j.val) := (regularizeValue_succ _ _).symm
        _ ≤ a.regularizeValue k := a.regularizeValue_monotone hk.1.le
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith
  · rw [ContinuousAt, SuccOrder.nhds_eq_pure.mpr hi]
    exact tendsto_pure_nhds _ _

end Profile
end BFPP
