import BFPP.ProfileRestriction
import BFPP.PrefixFactorization

/-! # Transfinite contractive propagators -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {κ : Ordinal.{u}}

noncomputable def inputPrefix (D : Set (BoundedFamily (OrdinalIndex κ))) (i : OrdinalIndex κ)
    (x : D) : BoundedFamily (OrdinalIndex i.val) := restrictFamily i.property.le x.val

noncomputable def prefixLift (D : Set (BoundedFamily (OrdinalIndex κ))) (i : OrdinalIndex κ)
    (x : D) : range (inputPrefix D i) := ⟨inputPrefix D i x, mem_range_self x⟩

/-- The successor rules are defined on exactly the prefixes arising from the domain.
The sign of the envelope at each limit is fixed independently of the input. -/
structure IsTCP (D : Set (BoundedFamily (OrdinalIndex κ))) (P : D → D) : Prop where
  positive : 0 < κ
  nonempty : D.Nonempty
  at_zero : ∃ c : ℝ, ∀ x, (P x).val ⟨0, positive⟩ = c
  successor_rules : ∀ i : OrdinalIndex κ, i.val ∈ range (Order.succ : Ordinal.{u} → Ordinal.{u}) →
    ∃ Φ : range (inputPrefix D i) → ℝ, LipschitzWith 1 Φ ∧
      ∀ x, Φ (prefixLift D i x) = (P x).val i
  limit_rules : ∀ i : OrdinalIndex κ, IsSuccLimit i.val →
    ∃ ε : Bool, ∀ x, (P x).val i =
      if ε then upperEnvelope (inputPrefix D i x) else lowerEnvelope (inputPrefix D i x)

theorem inputPrefix_dist_le (D : Set (BoundedFamily (OrdinalIndex κ))) (i : OrdinalIndex κ)
    (x y : D) : dist (inputPrefix D i x) (inputPrefix D i y) ≤ dist x y := by
  change dist (restrictFamily i.property.le x.val) (restrictFamily i.property.le y.val) ≤
    dist x.val y.val
  simpa only [NNReal.coe_one, one_mul] using
    (restrictFamily_nonexpansive i.property.le).dist_le_mul x.val y.val

theorem IsTCP.nonexpansive {D : Set (BoundedFamily (OrdinalIndex κ))} {P : D → D}
    (h : IsTCP D P) : LipschitzWith 1 P := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  change dist (P x).val (P y).val ≤ dist x y
  apply (BoundedFamily.dist_le_iff _ _ dist_nonneg).mpr
  intro i
  rcases Ordinal.zero_or_succ_or_isSuccLimit i.val with hi | hi | hi
  · obtain ⟨c, hc⟩ := h.at_zero
    have he : i = ⟨0, h.positive⟩ := Subtype.ext hi
    rw [he, hc x, hc y, sub_self, abs_zero]
    exact dist_nonneg
  · obtain ⟨Φ, hΦ, hΦeq⟩ := h.successor_rules i hi
    have hh := hΦ.dist_le_mul (prefixLift D i x) (prefixLift D i y)
    have hb : |(P x).val i - (P y).val i| ≤ dist (inputPrefix D i x) (inputPrefix D i y) := by
      change |(P x).val i - (P y).val i| ≤ dist (prefixLift D i x) (prefixLift D i y)
      simpa only [NNReal.coe_one, one_mul, hΦeq, Real.dist_eq] using hh
    exact hb.trans (inputPrefix_dist_le D i x y)
  · letI : Nonempty (OrdinalIndex i.val) := ⟨⟨0, hi.pos⟩⟩
    obtain ⟨ε, hε⟩ := h.limit_rules i hi
    have hb : |(P x).val i - (P y).val i| ≤ dist (inputPrefix D i x) (inputPrefix D i y) := by
      rw [hε x, hε y]
      cases ε
      · simpa only [Bool.false_eq_true, ite_false, NNReal.coe_one, one_mul, Real.dist_eq] using
          lowerEnvelope_nonexpansive.dist_le_mul (inputPrefix D i x) (inputPrefix D i y)
      · simpa only [ite_true, NNReal.coe_one, one_mul, Real.dist_eq] using
          upperEnvelope_nonexpansive.dist_le_mul (inputPrefix D i x) (inputPrefix D i y)
    exact hb.trans (inputPrefix_dist_le D i x y)

theorem isTCP_of_causal {D : Set (BoundedFamily (OrdinalIndex κ))} (P : D → D)
    (hpos : 0 < κ) (hne : D.Nonempty) (c : ℝ) (hzero : ∀ x, (P x).val ⟨0, hpos⟩ = c)
    (hcausal : ∀ i x y, dist ((P x).val i) ((P y).val i) ≤
      dist (inputPrefix D i x) (inputPrefix D i y))
    (hlimit : ∀ i, IsSuccLimit i.val → ∀ x,
      (P x).val i = lowerEnvelope (inputPrefix D i x)) : IsTCP D P := by
  refine ⟨hpos, hne, ⟨c, hzero⟩, ?_, ?_⟩
  · intro i _
    exact exists_nonexpansive_factor (fun x => (P x).val i) (inputPrefix D i) (hcausal i)
  · intro i hi
    exact ⟨false, fun x => hlimit i hi x⟩

end BFPP
