import BFPP.PointwisePrefixes

/-! # An infinite initial ordinal with a discontinuous terminal pointwise supremum -/

namespace BFPP

set_option autoImplicit false
open Set Order Cardinal unitInterval

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- The appendix construction only needs an open set which is not closed.
The codomain `I` is the actual closed real interval `[0,1]`. -/
theorem exists_terminal_pointwise_supremum (U : Set K) (hU : IsOpen U) (hclosed : ¬ IsClosed U) :
    ∃ η : Cardinal.{u}, ℵ₀ ≤ η ∧ ∃ hη : IsSuccLimit η.ord,
      ∃ (s : OrdinalIndex η.ord → C(K, I)) (sstar : K → I),
        Monotone (fun i t => s i t) ∧ s ⟨0, hη.pos⟩ = 0 ∧
        (∀ i : OrdinalIndex η.ord, IsSuccLimit i.val → ∀ t,
          s i t = ⨆ j : Iio i, s j.val t) ∧
        (∀ t, sstar t = ⨆ i, s i t) ∧ ¬ Continuous sstar := by
  classical
  obtain ⟨S, hS, hinf, hmin⟩ := exists_minimal_discontinuous_family U hU hclosed
  let η : Cardinal.{u} := #S
  have hη : IsSuccLimit η.ord := Cardinal.isSuccLimit_ord hinf
  letI : Fact (IsSuccLimit η.ord) := ⟨hη⟩
  let e : η.ord.ToType ≃ S := (Cardinal.eq.mp (by simp [η])).some
  let eo : OrdinalIndex η.ord ≃o η.ord.ToType := Ordinal.ToType.mk
  let g : η.ord.ToType → C(K, I) := fun i => (e i).val
  let go : OrdinalIndex η.ord → C(K, I) := g ∘ eo
  have hcont : ∀ i : η.ord.ToType, Continuous (pointwisePrefix g i) := by
    intro i
    rw [pointwisePrefix_image]
    apply hmin
    have hi : #(Iio i) < η := by
      simpa only [Cardinal.mk_ord_toType] using
        (Cardinal.mk_Iio_lt i (by simp))
    exact Cardinal.mk_image_le.trans_lt hi
  let s : OrdinalIndex η.ord → C(K, I) := fun i => ⟨pointwisePrefix g (eo i), hcont (eo i)⟩
  have hs : ∀ i, (s i : K → I) = pointwisePrefix go i := by
    intro i
    exact (pointwisePrefix_reindex eo g i).symm
  have htotal : ∀ t, (⨆ i, go i t) = pointwiseSup S t := by
    intro t
    apply le_antisymm
    · refine iSup_le fun i => ?_
      exact le_iSup_of_le (go i) (le_iSup_of_le (e (eo i)).property le_rfl)
    · refine iSup_le fun f => iSup_le fun hf => ?_
      obtain ⟨j, hj⟩ := e.surjective ⟨f, hf⟩
      obtain ⟨i, hi⟩ := eo.surjective j
      exact le_iSup_of_le i (by simp [go, g, Function.comp_def, hi, hj])
  refine ⟨η, hinf, hη, s, pointwiseSup S, ?_, ?_, ?_, ?_, hS⟩
  · intro i j hij t
    change s i t ≤ s j t
    rw [show s i t = pointwisePrefix go i t from congrFun (hs i) t,
      show s j t = pointwisePrefix go j t from congrFun (hs j) t]
    exact pointwisePrefix_mono go hij t
  · apply ContinuousMap.ext
    intro t
    have hz := congrFun (pointwisePrefix_bot go) t
    exact (congrFun (hs ⟨0, hη.pos⟩) t).trans hz
  · intro i hi t
    have hbetween : ∀ j : OrdinalIndex η.ord, j < i → ∃ k, j < k ∧ k < i := by
      intro j hj
      have hji : j.val < i.val := hj
      have hsucc : succ j.val < i.val := hi.succ_lt hji
      exact ⟨⟨succ j.val, hsucc.trans i.property⟩, Order.lt_succ j.val, hsucc⟩
    calc
      s i t = pointwisePrefix go i t := congrFun (hs i) t
      _ = ⨆ j : Iio i, pointwisePrefix go j.val t := pointwisePrefix_limit go i hbetween t
      _ = ⨆ j : Iio i, s j.val t := by
        apply iSup_congr
        intro j
        exact (congrFun (hs j.val) t).symm
  · intro t
    calc
      pointwiseSup S t = ⨆ i, go i t := (htotal t).symm
      _ = ⨆ i, pointwisePrefix go i t := (pointwisePrefix_terminal go t).symm
      _ = ⨆ i, s i t := by
        apply iSup_congr
        intro i
        exact (congrFun (hs i) t).symm

theorem exists_terminal_pointwise_supremum_of_not_ED (hK : ¬ ExtremallyDisconnected K) :
    ∃ η : Cardinal.{u}, ℵ₀ ≤ η ∧ ∃ hη : IsSuccLimit η.ord,
      ∃ (s : OrdinalIndex η.ord → C(K, I)) (sstar : K → I),
        Monotone (fun i t => s i t) ∧ s ⟨0, hη.pos⟩ = 0 ∧
        (∀ i : OrdinalIndex η.ord, IsSuccLimit i.val → ∀ t,
          s i t = ⨆ j : Iio i, s j.val t) ∧
        (∀ t, sstar t = ⨆ i, s i t) ∧ ¬ Continuous sstar := by
  obtain ⟨U, hU, hc⟩ := exists_open_not_closed_of_not_ED hK
  exact exists_terminal_pointwise_supremum U hU hc

end BFPP
