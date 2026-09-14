import BFPP.Transfer
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! # The discrete affine propagation estimate in the introduction -/

namespace BFPP

set_option autoImplicit false

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coefficients and the translation are fixed independently of the input. -/
theorem affine_propagation_lipschitz (f g : X → E) (A B : NNReal)
    (hf : LipschitzWith A f) (hg : LipschitzWith B g) (a b : ℝ) (c : E) :
    LipschitzWith (‖a‖₊ * A + ‖b‖₊ * B) (fun x => a • f x + b • g x + c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' := hf.dist_le_mul x y
  have hg' := hg.dist_le_mul x y
  simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm]
  calc
    dist (a • f x + b • g x + c) (a • f y + b • g y + c) =
        dist (a • f x + b • g x) (a • f y + b • g y) := dist_add_right _ _ _
    _ ≤ dist (a • f x) (a • f y) + dist (b • g x) (b • g y) := dist_add_add_le _ _ _ _
    _ = ‖a‖ * dist (f x) (f y) + ‖b‖ * dist (g x) (g y) := by rw [dist_smul₀, dist_smul₀]
    _ ≤ ‖a‖ * (A * dist x y) + ‖b‖ * (B * dist x y) :=
      add_le_add (mul_le_mul_of_nonneg_left hf' (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hg' (norm_nonneg _))
    _ = (‖a‖ * A + ‖b‖ * B) * dist x y := by ring

theorem affine_propagation_nonexpansive (f g : X → E)
    (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) (a b : ℝ) (c : E)
    (hab : |a| + |b| ≤ 1) : LipschitzWith 1 (fun x => a • f x + b • g x + c) := by
  apply (affine_propagation_lipschitz f g 1 1 hf hg a b c).weaken
  exact_mod_cast (by simpa only [Real.norm_eq_abs, mul_one] using hab :
    ‖a‖ * (1 : ℝ) + ‖b‖ * 1 ≤ 1)

/-- The estimate at every step of the displayed discrete recurrence. -/
theorem discrete_recurrence_nonexpansive (S g : ℕ → X → E) (a b : ℕ → ℝ) (c : ℕ → E)
    (hrec : ∀ n x, S (n + 1) x = a n • S n x + b n • g n x + c n)
    (hzero : LipschitzWith 1 (S 0)) (hg : ∀ n, LipschitzWith 1 (g n))
    (hab : ∀ n, |a n| + |b n| ≤ 1) : ∀ n, LipschitzWith 1 (S n) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have he : S (n + 1) = fun x => a n • S n x + b n • g n x + c n := funext (hrec n)
    rw [he]
    exact affine_propagation_nonexpansive (S n) (g n) ih (hg n) (a n) (b n) (c n) (hab n)

end BFPP
