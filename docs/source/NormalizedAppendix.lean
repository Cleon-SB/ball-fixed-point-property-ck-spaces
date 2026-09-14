import BFPP.TerminalNormalization

/-! # The appendix construction with terminal supremum norm one -/

namespace BFPP

set_option autoImplicit false
open Set Order Cardinal unitInterval

universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem unitInterval_coe_iSup {ι : Type v} [Nonempty ι] (f : ι → I) :
    ((⨆ i, f i : I) : ℝ) = ⨆ i, (f i : ℝ) :=
  Set.Icc.coe_iSup (by norm_num)

theorem exists_normalized_terminal_supremum (hK : ¬ ExtremallyDisconnected K) :
    ∃ η : Cardinal.{u}, ℵ₀ ≤ η ∧ ∃ hη : IsSuccLimit η.ord,
      ∃ (s : OrdinalIndex η.ord → C(K, ℝ)) (sstar : BoundedFamily K),
        Monotone (fun i t => s i t) ∧ s ⟨0, hη.pos⟩ = 0 ∧
        (∀ i t, 0 ≤ s i t ∧ s i t ≤ 1) ∧
        (∀ i : OrdinalIndex η.ord, IsSuccLimit i.val → ∀ t,
          s i t = ⨆ j : Iio i, s j.val t) ∧
        (∀ t, sstar t = ⨆ i, s i t) ∧ (∀ t, 0 ≤ sstar t ∧ sstar t ≤ 1) ∧
        ‖sstar‖ = 1 ∧ ¬ Continuous (fun t => sstar t) := by
  obtain ⟨η, hinf, hη, s, f, hmono, hzero, hlim, hterminal, hdisc⟩ :=
    exists_terminal_pointwise_supremum_of_not_ED hK
  letI : Fact (IsSuccLimit η.ord) := ⟨hη⟩
  let a : ℝ := ‖boundedUnitFunction f‖⁻¹
  have ha : 0 < a := inv_pos.mpr (terminal_norm_pos f hdisc)
  let sn : OrdinalIndex η.ord → C(K, ℝ) := fun i =>
    ⟨fun t => a * (s i t : ℝ), normalized_profile_continuous f (s i)⟩
  have hsle : ∀ i t, s i t ≤ f t := by
    intro i t
    rw [hterminal t]
    exact le_iSup (fun j => s j t) i
  have hbdd : ∀ t, BddAbove (range (fun i => (s i t : ℝ))) := by
    intro t
    exact ⟨1, fun _ ⟨i, hi⟩ => hi ▸ (s i t).property.2⟩
  refine ⟨η, hinf, hη, sn, normalizedTerminal f, ?_, ?_, ?_, ?_, ?_,
    normalizedTerminal_bounds f hdisc, normalizedTerminal_norm f hdisc,
    normalizedTerminal_not_continuous f hdisc⟩
  · intro i j hij t
    change a * (s i t : ℝ) ≤ a * (s j t : ℝ)
    exact mul_le_mul_of_nonneg_left (hmono hij t) ha.le
  · apply ContinuousMap.ext
    intro t
    change a * (s ⟨0, hη.pos⟩ t : ℝ) = 0
    rw [hzero]
    simp
  · intro i t
    exact normalized_profile_bounds f hdisc (s i) (hsle i) t
  · intro i hi t
    letI : Nonempty (Iio i) := ⟨⟨⟨0, hη.pos⟩, hi.pos⟩⟩
    have he : (s i t : ℝ) = ⨆ j : Iio i, (s j.val t : ℝ) := by
      rw [hlim i hi t]
      exact unitInterval_coe_iSup _
    change a * (s i t : ℝ) = ⨆ j : Iio i, a * (s j.val t : ℝ)
    rw [he]
    apply positive_scale_ciSup a ha
    exact ⟨1, fun _ ⟨j, hj⟩ => hj ▸ (s j.val t).property.2⟩
  · intro t
    have he : (f t : ℝ) = ⨆ i, (s i t : ℝ) := by
      rw [hterminal t]
      exact unitInterval_coe_iSup _
    change a * (f t : ℝ) = ⨆ i, a * (s i t : ℝ)
    rw [he]
    exact positive_scale_ciSup a ha _ (hbdd t)

end BFPP
