import BFPP.BooleanGap
import BFPP.CofinalSequences

/-! # Cofinal ordinal coordinates for a lattice gap -/

namespace BFPP

set_option autoImplicit false
open Set Order

universe u v w
variable (B : Type u) (ι : Type v) (κ : Type w)
  [Lattice B] [BoundedOrder B] [LinearOrder ι] [OrderBot ι] [LinearOrder κ] [OrderBot κ]

structure IndexedGap where
  lower : ι → B
  upper : κ → B
  lower_mono : Monotone lower
  upper_anti : Antitone upper
  lower_bot : lower ⊥ = ⊥
  upper_bot : upper ⊥ = ⊤
  cross : ∀ i j, lower i ≤ upper j
  no_interpolant : ¬ ∃ b, (∀ i, lower i ≤ b) ∧ ∀ j, b ≤ upper j

namespace ChainGap

variable {B ι κ}

noncomputable instance lowerLinearOrder (g : ChainGap B) : LinearOrder g.lower := by
  classical
  exact { Subtype.partialOrder _ with
    le_total := fun a b => g.lower_chain.total a.property b.property
    toDecidableLE := Classical.decRel _ }

noncomputable instance upperLinearOrder (g : ChainGap B) : LinearOrder g.upper := by
  classical
  exact { Subtype.partialOrder _ with
    le_total := fun a b => g.upper_chain.total a.property b.property
    toDecidableLE := Classical.decRel _ }

instance lowerOrderBot (g : ChainGap B) : OrderBot g.lower := Subtype.orderBot g.bot_mem
instance upperOrderTop (g : ChainGap B) : OrderTop g.upper := Subtype.orderTop g.top_mem

instance lowerNoMaxOrder (g : ChainGap B) : NoMaxOrder g.lower := ⟨by
  intro a
  obtain ⟨b, hb, hab⟩ := g.lower_no_max a.val a.property
  exact ⟨⟨b, hb⟩, hab⟩⟩

instance upperNoMinOrder (g : ChainGap B) : NoMinOrder g.upper := ⟨by
  intro a
  obtain ⟨b, hb, hab⟩ := g.upper_no_min a.val a.property
  exact ⟨⟨b, hb⟩, hab⟩⟩

theorem exists_indexedGap (g : ChainGap B) :
    ∃ ρ σ : Ordinal.{u}, ∃ hρ : IsSuccLimit ρ, ∃ hσ : IsSuccLimit σ,
      ρ.cof.ord = ρ ∧ σ.cof.ord = σ ∧
      @Nonempty (@IndexedGap B (OrdinalIndex ρ) (OrdinalIndex σ) _ _ _
        (@ordinalIndexOrderBot ρ ⟨hρ⟩) _ (@ordinalIndexOrderBot σ ⟨hσ⟩)) := by
  obtain ⟨ρ, hρ, hregρ, f, hf, hf₀, hfcof⟩ := exists_regular_cofinal_sequence_from_bot g.lower
  obtain ⟨σ, hσ, hregσ, h, hh, hh₀, hhcof⟩ :=
    exists_regular_cofinal_sequence_from_bot (OrderDual g.upper)
  letI : Fact (IsSuccLimit ρ) := ⟨hρ⟩
  letI : Fact (IsSuccLimit σ) := ⟨hσ⟩
  refine ⟨ρ, σ, hρ, hσ, hregρ, hregσ, ⟨{
    lower := fun i => (f i).val
    upper := fun j => (h j).val
    lower_mono := fun _ _ hij => hf hij
    upper_anti := fun _ _ hij => hh hij
    lower_bot := ?_
    upper_bot := ?_
    cross := fun i j => g.cross _ (f i).property _ (h j).property
    no_interpolant := ?_ }⟩⟩
  · exact congrArg Subtype.val hf₀
  · exact congrArg Subtype.val hh₀
  · rintro ⟨b, hfb, hbh⟩
    apply g.no_interpolant
    refine ⟨b, ?_, ?_⟩
    · intro y hy
      obtain ⟨_, ⟨i, rfl⟩, hyi⟩ := hfcof ⟨y, hy⟩
      change y ≤ (f i).val at hyi
      exact hyi.trans (hfb i)
    · intro z hz
      obtain ⟨_, ⟨j, rfl⟩, hjz⟩ := hhcof ⟨z, hz⟩
      change (h j).val ≤ z at hjz
      exact (hbh j).trans hjz

end ChainGap
end BFPP
