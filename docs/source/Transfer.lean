import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Contractive realization and fixed-point transfer

This file formalizes the transfer and order-domination statements in Section 2
of `csb-BFPP-JFA.tex`. No existence assumption about a realization is discharged
here: the later construction must supply the maps and their estimates.
-/

namespace BFPP

set_option autoImplicit false

universe u v

variable {X : Type u} {D : Type v}

/-- The fixed points of the two cyclic composites are canonically equivalent. -/
def fixedPointEquiv (A : X → D) (J : D → X) (P : D → D) :
    {x : X // J (P (A x)) = x} ≃ {z : D // A (J (P z)) = z} where
  toFun x := ⟨A x, congrArg A x.property⟩
  invFun z := ⟨J (P z), congrArg (fun w => J (P w)) z.property⟩
  left_inv x := Subtype.ext x.property
  right_inv z := Subtype.ext z.property

theorem exists_fixedPoint_iff (A : X → D) (J : D → X) (P : D → D) :
    (∃ x, J (P (A x)) = x) ↔ ∃ z, A (J (P z)) = z := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨A x, congrArg A hx⟩
  · rintro ⟨z, hz⟩
    exact ⟨J (P z), congrArg (fun w => J (P w)) hz⟩

/-- The fixed-point hypothesis concerns the cyclic composite, not just `P`. -/
theorem fixedPointFree_transfer (A : X → D) (J : D → X) (P : D → D)
    (h : ∀ z, A (J (P z)) ≠ z) : ∀ x, J (P (A x)) ≠ x := by
  intro x hx
  exact h (A x) (congrArg A hx)

/-- Order domination supplies the required fixed-point-free cyclic composite. -/
theorem order_domination [Preorder D] (A : X → D) (J : D → X) (P : D → D)
    (hAJ : ∀ z, A (J z) ≤ z) (hP : ∀ z, ¬ z ≤ P z) :
    ∀ z, A (J (P z)) ≠ z := by
  intro z hz
  apply hP z
  calc
    z = A (J (P z)) := hz.symm
    _ ≤ P z := hAJ (P z)

theorem fixedPointFree_of_order_domination [Preorder D]
    (A : X → D) (J : D → X) (P : D → D)
    (hAJ : ∀ z, A (J z) ≤ z) (hP : ∀ z, ¬ z ≤ P z) :
    ∀ x, J (P (A x)) ≠ x :=
  fixedPointFree_transfer A J P (order_domination A J P hAJ hP)

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace D]

theorem nonexpansive_transfer (A : X → D) (J : D → X) (P : D → D)
    (hA : LipschitzWith 1 A) (hJ : LipschitzWith 1 J) (hP : LipschitzWith 1 P) :
    LipschitzWith 1 (fun x => J (P (A x))) := by
  simpa only [mul_one, Function.comp_def] using hJ.comp (hP.comp hA)

theorem contractive_realization [Preorder D]
    (A : X → D) (J : D → X) (P : D → D)
    (hA : LipschitzWith 1 A) (hJ : LipschitzWith 1 J) (hP : LipschitzWith 1 P)
    (hAJ : ∀ z, A (J z) ≤ z) (hsub : ∀ z, ¬ z ≤ P z) :
    LipschitzWith 1 (fun x => J (P (A x))) ∧ ∀ x, J (P (A x)) ≠ x :=
  ⟨nonexpansive_transfer A J P hA hJ hP,
    fixedPointFree_of_order_domination A J P hAJ hsub⟩

end Metric

/-- The closed unit ball, with the metric inherited from the normed space. -/
abbrev UnitBall (X : Type u) [SeminormedAddCommGroup X] := {x : X // ‖x‖ ≤ 1}

/-- Ball fixed point property for the given norm (the unit-ball formulation). -/
def HasBFPP (X : Type u) [SeminormedAddCommGroup X] : Prop :=
  ∀ T : UnitBall X → UnitBall X, LipschitzWith 1 T → ∃ x, T x = x

theorem not_hasBFPP_of_fixedPointFree [SeminormedAddCommGroup X]
    (T : UnitBall X → UnitBall X) (hT : LipschitzWith 1 T)
    (hfree : ∀ x, T x ≠ x) : ¬ HasBFPP X := by
  intro h
  obtain ⟨x, hx⟩ := h T hT
  exact hfree x hx

end BFPP
