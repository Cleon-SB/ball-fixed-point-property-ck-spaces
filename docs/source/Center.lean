import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! # The common center and sharp scalar clamp estimates -/

namespace BFPP

set_option autoImplicit false

noncomputable def commonCenter (A B : ℝ) : ℝ := (B - A) / 2

theorem commonCenter_bounds {A B : ℝ} (hA : 0 ≤ A ∧ A ≤ 2)
    (hB : 0 ≤ B ∧ B ≤ 2) (hAB : 2 ≤ A + B) :
    -1 ≤ commonCenter A B ∧ commonCenter A B ≤ 1 ∧
    1 - A ≤ commonCenter A B ∧ commonCenter A B ≤ B - 1 := by
  dsimp [commonCenter]
  obtain ⟨hA0, hA2⟩ := hA
  obtain ⟨hB0, hB2⟩ := hB
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem commonCenter_nonexpansive_bound {A B A' B' d : ℝ}
    (hA : |A - A'| ≤ d) (hB : |B - B'| ≤ d) :
    |commonCenter A B - commonCenter A' B'| ≤ d := by
  rcases abs_le.mp hA with ⟨hA₁, hA₂⟩
  rcases abs_le.mp hB with ⟨hB₁, hB₂⟩
  apply abs_le.mpr
  dsimp [commonCenter]
  exact ⟨by linarith, by linarith⟩

theorem max_nonexpansive_bound {r s r' s' d : ℝ}
    (hr : |r - r'| ≤ d) (hs : |s - s'| ≤ d) :
    |max r s - max r' s'| ≤ d := by
  rcases abs_le.mp hr with ⟨hr₁, hr₂⟩
  rcases abs_le.mp hs with ⟨hs₁, hs₂⟩
  have h₁ : max r s ≤ max r' s' + d :=
    max_le (by linarith [le_max_left r' s']) (by linarith [le_max_right r' s'])
  have h₂ : max r' s' ≤ max r s + d :=
    max_le (by linarith [le_max_left r s]) (by linarith [le_max_right r s])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem min_nonexpansive_bound {r s r' s' d : ℝ}
    (hr : |r - r'| ≤ d) (hs : |s - s'| ≤ d) :
    |min r s - min r' s'| ≤ d := by
  rcases abs_le.mp hr with ⟨hr₁, hr₂⟩
  rcases abs_le.mp hs with ⟨hs₁, hs₂⟩
  have h₁ : min r s - d ≤ min r' s' :=
    le_min (by linarith [min_le_left r s]) (by linarith [min_le_right r s])
  have h₂ : min r' s' - d ≤ min r s :=
    le_min (by linarith [min_le_left r' s']) (by linarith [min_le_right r' s'])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem positive_tail_vanishes {A B : ℝ} (h : 2 ≤ A + B) :
    max (1 - A - commonCenter A B) 0 = 0 := by
  apply max_eq_right
  dsimp [commonCenter]
  linarith

theorem negative_tail_vanishes {A B : ℝ} (h : 2 ≤ A + B) :
    max (1 - B + commonCenter A B) 0 = 0 := by
  apply max_eq_right
  dsimp [commonCenter]
  linarith

end BFPP
