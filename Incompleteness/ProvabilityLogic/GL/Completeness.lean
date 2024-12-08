import Incompleteness.ProvabilityLogic.GL.SolovaySentences

namespace LO

open Classical

open System (Consistent)
open Modal
open FirstOrder.DerivabilityCondition
open ProvabilityLogic


variable {T : FirstOrder.Theory ℒₒᵣ}
variable {𝔅 : ProvabilityPredicate T T} [𝔅.HBL]

namespace Modal.Hilbert.GL

open FirstOrder.Theory (standardDP)

theorem arithmetical_completeness [System.Consistent T] : (∀ {f : Realization _ _}, T ⊢!. f.interpret 𝔅 A) → (Hilbert.GL ℕ) ⊢! A := by
  contrapose;
  intro h;
  obtain ⟨M, h⟩ := @Hilbert.GL.Kripke.unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree A |>.mp h;
  letI Φ := M↧.solovaySentences 𝔅;
  push_neg;
  use Φ.realization;
  exact SolovaySentences.lemma3 Φ h;

instance {T : FirstOrder.Theory ℒₒᵣ} [System.Consistent T] [𝐈𝚺₁ ≼ T] [T.Delta1Definable] : ArithmeticalComplete (Hilbert.GL ℕ) (standardDP T T) := ⟨arithmetical_completeness⟩

end Modal.Hilbert.GL


end LO
