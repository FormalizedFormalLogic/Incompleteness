import Incompleteness.Arith.DC
import Incompleteness.DC.Basic
import Logic.Modal.Hilbert

namespace LO.ProvabilityLogic

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal

variable {α : Type u} [DecidableEq α]
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T U : Theory L}

/-- Mapping modal prop vars to first-order sentence -/
def realization (α : Type u) (L) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def interpretation
  {T U : FirstOrder.Theory L}
  (f : realization α L) (𝔟 : ProvabilityPredicate T U) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | □p => ⦍𝔟⦎(interpretation f 𝔟 p)
  | ⊥ => ⊥
  | p ⟶ q => (interpretation f 𝔟 p) ⟶ (interpretation f 𝔟 q)
scoped notation f "[" 𝔟 "] " p => interpretation f 𝔟 p -- TODO: more good notation

namespace interpretation

end interpretation

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class ArithmeticalSoundness (Λ : Hilbert α) (𝔟 : ProvabilityPredicate T U) where
  sound : ∀ {p}, (Λ ⊢! p) → (∀ f, U ⊢!. (f[𝔟] p))

class ArithmeticalCompleteness (Λ : Hilbert α) (𝔟 : ProvabilityPredicate T U) where
  complete : ∀ {p}, (∀ f, U ⊢!. (f[𝔟] p)) → (Λ ⊢! p)


section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [DecidableEq (Sentence L)]
         {T U : FirstOrder.Theory L} [T ≼ U] [Diagonalization T]
         {𝔟 : ProvabilityPredicate T U}

lemma arithmetical_soundness_N [𝔟.HBL T₀ T] (h : 𝐍 ⊢! p) : ∀ {f : realization L α}, T ⊢!. (f[𝔟] p) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => simp at hp;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp =>
    simp only [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [interpretation]; trivial;

lemma arithmetical_soundness_GL [𝔟.HBL] (h : 𝐆𝐋 ⊢! p) : ∀ {f : realization α L}, U ⊢!. (f[𝔟] p) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp =>
    simp [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [interpretation]; trivial;

end ArithmeticalSoundness


section

instance (T : Theory ℒₒᵣ) [𝐈𝚺₁ ≼ T] [T.Delta1Definable]
  : ArithmeticalSoundness (𝐆𝐋 : Hilbert α) (T.standardDP T) := ⟨arithmetical_soundness_GL⟩

end


end LO.ProvabilityLogic
