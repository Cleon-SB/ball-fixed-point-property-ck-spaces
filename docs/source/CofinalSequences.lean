import BFPP.OrdinalIndex
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-! # Cofinal sequences indexed by regular limit ordinals -/

namespace BFPP

set_option autoImplicit false
open Set Order Ordinal Cardinal

universe u
variable (A : Type u) [LinearOrder A] [Nonempty A] [NoMaxOrder A]

theorem exists_regular_cofinal_sequence :
    ∃ τ : Ordinal.{u}, IsSuccLimit τ ∧ τ.cof.ord = τ ∧
      ∃ f : Iio τ → A, StrictMono f ∧ IsCofinal (range f) := by
  classical
  let R : Set A := {a | ∀ b, WellOrderingRel b a → b < a}
  have hR : IsCofinal R := isCofinal_setOfPred_imp_lt WellOrderingRel
  have hrel : ∀ a b : R, a < b → WellOrderingRel a.val b.val := by
    intro a b hab
    rcases trichotomous_of WellOrderingRel a.val b.val with hr | heq | hr
    · exact hr
    · exact (ne_of_lt hab (Subtype.ext heq)).elim
    · exact ((a.property b.val hr).not_gt hab).elim
  letI : WellFoundedLT R := ⟨(InvImage.wf Subtype.val WellOrderingRel.isWellOrder.wf).mono
    (fun {a b} hab => hrel a b hab)⟩
  letI : Nonempty R := hR.nonempty.to_subtype
  letI : NoMaxOrder R := ⟨by
    intro a
    obtain ⟨b, hab⟩ := exists_gt a.val
    obtain ⟨c, hc, hbc⟩ := hR b
    exact ⟨⟨c, hc⟩, hab.trans_le hbc⟩⟩
  obtain ⟨S, hS, htype⟩ := Ordinal.exists_ord_cof_eq R
  letI : Nonempty S := hS.nonempty.to_subtype
  letI : NoMaxOrder S := ⟨by
    intro a
    obtain ⟨b, hab⟩ := exists_gt a.val
    obtain ⟨c, hc, hbc⟩ := hS b
    exact ⟨⟨c, hc⟩, hab.trans_le hbc⟩⟩
  let τ := typeLT S
  have hlimit : IsSuccLimit τ := by
    apply Ordinal.one_lt_cof_iff.mp
    rw [Ordinal.cof_type]
    exact Order.one_lt_cof
  have hregular : τ.cof.ord = τ := by
    change (typeLT S).cof.ord = typeLT S
    rw [htype, Order.cof_ord_cof]
  let e : Iio τ ≃o S := OrderIso.ofRelIsoLT (Ordinal.enum (α := S) (· < ·))
  let f : Iio τ → A := fun i => (e i).val.val
  refine ⟨τ, hlimit, hregular, f, ?_, ?_⟩
  · intro i j hij
    exact e.strictMono hij
  · intro a
    obtain ⟨b, hb, hab⟩ := hR a
    obtain ⟨c, hc, hbc⟩ := hS ⟨b, hb⟩
    refine ⟨c.val, ⟨e.symm ⟨c, hc⟩, ?_⟩, hab.trans hbc⟩
    simp [f]

variable [OrderBot A]

theorem exists_regular_cofinal_sequence_from_bot :
    ∃ τ : Ordinal.{u}, ∃ hτ : IsSuccLimit τ, τ.cof.ord = τ ∧
      ∃ f : Iio τ → A, Monotone f ∧ f ⟨0, hτ.pos⟩ = ⊥ ∧ IsCofinal (range f) := by
  classical
  obtain ⟨τ, hτ, hreg, f, hf, hcof⟩ := exists_regular_cofinal_sequence A
  let g : Iio τ → A := fun i => if i.val = 0 then ⊥ else f i
  refine ⟨τ, hτ, hreg, g, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val = 0
    · simp only [g, if_pos hi]
      exact bot_le
    · have hj : j.val ≠ 0 := by
        intro hj
        exact hi (le_antisymm (hj ▸ hij) bot_le)
      simpa only [g, if_neg hi, if_neg hj] using hf.monotone hij
  · simp [g]
  · intro a
    obtain ⟨_, ⟨i, rfl⟩, hai⟩ := hcof a
    obtain ⟨j, hij⟩ := hτ.isSuccPrelimit.noMaxOrder_Iio.exists_gt i
    have hj : j.val ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hij)
    refine ⟨g j, mem_range_self j, ?_⟩
    simpa only [g, if_neg hj] using hai.trans (hf hij).le

end BFPP
