import BFPP.Families
import Mathlib.Order.Cofinal

/-! # Cofinal reindexing preserves inseparability -/

namespace BFPP

set_option autoImplicit false
open Set

universe u v w v' w'
variable {K : Type u} {ι : Type v} {κ : Type w} {ι' : Type v'} {κ' : Type w'}
  [TopologicalSpace K] [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]
  [LinearOrder ι'] [OrderBot ι'] [LinearOrder κ'] [OrderBot κ']

namespace IncreasingFamily

def reindex (F : IncreasingFamily K ι) (φ : ι' → ι) (hφ : Monotone φ) (h₀ : φ ⊥ = ⊥) :
    IncreasingFamily K ι' where
  functions i := F.functions (φ i)
  monotone t := (F.monotone t).comp hφ
  bounds i t := F.bounds (φ i) t
  at_bot := by rw [h₀, F.at_bot]

@[simp] theorem reindex_levels (F : IncreasingFamily K ι) (φ : ι' → ι)
    (hφ : Monotone φ) (h₀ : φ ⊥ = ⊥) (i : ι') :
    (F.reindex φ hφ h₀).levels i = F.levels (φ i) := rfl

theorem reindex_union (F : IncreasingFamily K ι) (φ : ι' → ι)
    (hφ : Monotone φ) (h₀ : φ ⊥ = ⊥) (hcof : IsCofinal (range φ)) :
    (⋃ i, (F.reindex φ hφ h₀).levels i) = ⋃ i, F.levels i := by
  ext t
  simp only [mem_iUnion, reindex_levels]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨φ i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨_, ⟨j, rfl⟩, hij⟩ := hcof i
    exact ⟨j, F.levels_monotone hij hi⟩

end IncreasingFamily

namespace InseparablePair

def reindex (F : InseparablePair K ι κ) (φ : ι' → ι) (ψ : κ' → κ)
    (hφ : Monotone φ) (hψ : Monotone ψ) (hφ₀ : φ ⊥ = ⊥) (hψ₀ : ψ ⊥ = ⊥)
    (hφcof : IsCofinal (range φ)) (hψcof : IsCofinal (range ψ)) : InseparablePair K ι' κ' where
  positive := F.positive.reindex φ hφ hφ₀
  negative := F.negative.reindex ψ hψ hψ₀
  orthogonal i j t := F.orthogonal (φ i) (ψ j) t
  inseparable := by
    rw [F.positive.reindex_union φ hφ hφ₀ hφcof, F.negative.reindex_union ψ hψ hψ₀ hψcof]
    exact F.inseparable

end InseparablePair
end BFPP
