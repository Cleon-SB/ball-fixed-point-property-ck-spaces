import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Real.Sqrt

/-! # Nonexpansive rules descend to the prefixes which actually occur -/

namespace BFPP

set_option autoImplicit false

theorem exists_nonexpansive_factor {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → ℝ) (G : X → Y) (h : ∀ x y, dist (f x) (f y) ≤ dist (G x) (G y)) :
    ∃ Φ : Set.range G → ℝ, LipschitzWith 1 Φ ∧
      ∀ x, Φ ⟨G x, Set.mem_range_self x⟩ = f x := by
  classical
  let Φ : Set.range G → ℝ := fun y => f y.property.choose
  refine ⟨Φ, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [NNReal.coe_one, one_mul]
    have hh := h y.property.choose z.property.choose
    rw [y.property.choose_spec, z.property.choose_spec] at hh
    exact hh
  · intro x
    change f (Set.mem_range_self (f := G) x).choose = f x
    apply dist_le_zero.mp
    have hh := h (Set.mem_range_self (f := G) x).choose x
    rw [(Set.mem_range_self (f := G) x).choose_spec, dist_self] at hh
    exact hh

end BFPP
