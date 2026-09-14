import BFPP.ExtensionDelay
import BFPP.InterleavingEnvelopes

/-! # Restriction to ordinal prefixes and the encoded limit formulas -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u
variable {tau κ : Ordinal.{u}}

noncomputable def restrictFamily (h : tau ≤ κ) (f : BoundedFamily (OrdinalIndex κ)) :
    BoundedFamily (OrdinalIndex tau) :=
  BoundedFamily.reindex (fun i => ⟨i.val, lt_of_lt_of_le i.property h⟩) f

@[simp] theorem restrictFamily_apply (h : tau ≤ κ) (f : BoundedFamily (OrdinalIndex κ))
    (i : OrdinalIndex tau) :
    restrictFamily h f i = f ⟨i.val, lt_of_lt_of_le i.property h⟩ := rfl

theorem restrictFamily_nonexpansive (h : tau ≤ κ) : LipschitzWith 1 (restrictFamily h) :=
  BoundedFamily.reindex_nonexpansive _

variable [Fact (IsSuccLimit tau)] [Fact (IsSuccLimit κ)]

noncomputable def Profile.restrict (h : tau ≤ κ) (a : Profile (OrdinalIndex κ)) :
    Profile (OrdinalIndex tau) := by
  refine ⟨restrictFamily h a.val, ?_, ?_, ?_⟩
  · exact a.at_bot
  · intro i j hij
    exact a.monotone hij
  · intro i
    exact ⟨a.nonneg _, a.le_two _⟩

@[simp] theorem Profile.restrict_apply (h : tau ≤ κ) (a : Profile (OrdinalIndex κ))
    (i : OrdinalIndex tau) :
    (a.restrict h).val i = a.val ⟨i.val, lt_of_lt_of_le i.property h⟩ := rfl

theorem Profile.tail_restrict (h : tau < κ) (a : Profile (OrdinalIndex κ)) :
    (a.restrict h.le).tail = a.delayValue ⟨tau, h⟩ := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    exact a.le_delayValue_of_lt ⟨i.val, lt_trans i.property h⟩ ⟨tau, h⟩ i.property
  · apply a.delayValue_le_of_forall_lt ⟨tau, h⟩ _ (a.restrict h.le).tail_nonneg
    intro j hj
    exact (a.restrict h.le).le_tail ⟨j.val, hj⟩

theorem restrictFamily_interleave (h : tau ≤ κ) (a b : Profile (OrdinalIndex κ)) :
    restrictFamily h (interleave a.val b.val) = interleave (a.restrict h).val (b.restrict h).val := by
  letI : TopologicalSpace (OrdinalIndex tau) := ⊥
  apply BoundedContinuousFunction.ext
  intro i
  rfl

theorem interleave_lowerEnvelope_prefix (h : tau < κ) (a b : Profile (OrdinalIndex κ)) :
    lowerEnvelope (restrictFamily h.le (interleave a.val b.val)) = a.delayValue ⟨tau, h⟩ := by
  rw [restrictFamily_interleave, interleave_lowerEnvelope, Profile.tail_restrict]

theorem interleave_upperEnvelope_prefix (h : tau < κ) (a b : Profile (OrdinalIndex κ)) :
    upperEnvelope (restrictFamily h.le (interleave a.val b.val)) = 4 + b.delayValue ⟨tau, h⟩ := by
  rw [restrictFamily_interleave, interleave_upperEnvelope, Profile.tail_restrict]

end BFPP
