import Incompleteness.ProvabilityLogic.Basic

namespace LO

open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open ProvabilityPredicate
open System
open ProvabilityLogic

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [T ≼ U]
         {𝔅 : ProvabilityPredicate T U}

namespace Modal.Hilbert

namespace N

theorem arithmetical_soundness (h : (Hilbert.N α) ⊢! φ) : ∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => simp at hp;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra_neg!;

end N


namespace GL

theorem arithmetical_soundness [Diagonalization T] [𝔅.HBL] (h : (Hilbert.GL α) ⊢! φ) : ∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra_neg!;

instance {T : FirstOrder.Theory ℒₒᵣ} [𝐈𝚺₁ ≼ T] [T.Delta1Definable] : ArithmeticalSound (Hilbert.GL α) (T.standardDP T) := ⟨arithmetical_soundness⟩

end GL

end Modal.Hilbert


end LO
