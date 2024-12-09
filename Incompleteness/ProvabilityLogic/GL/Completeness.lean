import Incompleteness.ProvabilityLogic.GL.SolovaySentences

namespace LO

open Classical

open System (Consistent)
open Modal
open FirstOrder.DerivabilityCondition
open ProvabilityLogic


variable {T : FirstOrder.Theory ℒₒᵣ} [𝐑₀ ≼ T] [𝐈𝚺₁ ≼ T] [System.Consistent T] [T.Delta1Definable] [ℕ ⊧ₘ* T]

namespace Modal.Hilbert.GL

open FirstOrder.Theory (standardDP)

theorem arithmetical_completeness : (∀ {f : Realization _ _}, T ⊢!. f.interpret (standardDP T T) A) → (Hilbert.GL ℕ) ⊢! A := by
  contrapose;
  intro h;
  obtain ⟨M, h⟩ := @Hilbert.GL.Kripke.unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree A |>.mp h;
  letI Φ := M↧.solovaySentences (standardDP T T);
  push_neg;
  use Φ.realization;
  refine SolovaySentences.lemma3 Φ h ?_;
  . intro k hk;
    apply FirstOrder.Arith.provableₐ_sound (T := T) (U := T);
    exact hk;

instance : ArithmeticalComplete (Hilbert.GL ℕ) (standardDP T T) := ⟨arithmetical_completeness⟩

end Modal.Hilbert.GL


end LO
