import Incompleteness.Arith.DC
import Incompleteness.DC.Basic
import Logic.Modal.Hilbert

namespace LO.ProvabilityLogic

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal

variable {α : Type*} [DecidableEq α]

/-- Mapping modal prop vars to first-order sentence -/
def realization (L) (α : Type u) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def interpretation
  [Semiterm.Operator.GoedelNumber L (FirstOrder.Sentence L)]
  (f : realization L α) (𝔟 : ProvabilityPredicate L L) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | □p => ⦍𝔟⦎(interpretation f 𝔟 p)
  | ⊥ => ⊥
  | p ⟶ q => (interpretation f 𝔟 p) ⟶ (interpretation f 𝔟 q)
scoped notation f "[" 𝔟 "] " p => interpretation f 𝔟 p -- TODO: more good notation

namespace interpretation

variable [Semiterm.Operator.GoedelNumber L (FirstOrder.Sentence L)]
         {f : realization L α} {𝔟 : ProvabilityPredicate L L} {p q : Formula α}
         [NegAbbrev (FirstOrder.Sentence L)]

lemma imp_def : (f[𝔟] (p ⟶ q)) = ((f[𝔟] p) ⟶ (f[𝔟] q)) := by rfl
lemma box_def : (f[𝔟] □p) = ⦍𝔟⦎(f[𝔟] p) := by rfl
lemma neg_def : (f[𝔟] ~p) = (f[𝔟] p) ⟶ ⊥ := by rfl

end interpretation

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

/-
class ArithmeticalSoundness (Λ : Hilbert α) (𝔟 : ProvabilityPredicate L L) where
  sound : ∀ {p}, (Λ ⊢! p) → (∀ f, T ⊢!. (f[𝔟] p))

class ArithmeticalSoundness₂ (Λ : Hilbert α) (T₀ T : Theory L) where
  prov : ProvabilityPredicate L L
  sound : ∀ {p}, (Λ ⊢! p) → (∀ f, T ⊢!. (f[prov] p))

class ArithmeticalCompleteness (Λ : Hilbert α) (𝔟 : ProvabilityPredicate L L) where
  prov : ProvabilityPredicate L L
  complete : ∀ {p}, (∀ f, T ⊢!. (f[𝔟] p)) → (Λ ⊢! p)

  TODO:
  `ArithmeticalSoundness`と`ArithmeticalCompleteness`を単純にinstance化する際には大抵`T₀`に依存してしまうため型推論が壊れてしまう．
  もう少し良いやり方がありそうな気もするので一旦コメントアウト
section

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
variable (α) (𝔟 : ProvabilityPredicate L L)

class ArithmeticalSoundness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  sound : ∀ {p}, (𝓓 ⊢! p) → (∀ f, T ⊢! f[𝔟] p)

class ArithmeticalCompleteness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  complete : ∀ {p}, (∀ f, T ⊢! f[𝔟] p) → (𝓓 ⊢! p)

class ProvabilityLogic (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L)where
  is : System.theory 𝓓 = { p | ∀ f, T ⊢! f[𝔟] p }

variable {α 𝔟} {𝓓 : DeductionParameter α} {T : FirstOrder.Theory L}

instance [ArithmeticalSoundness α 𝔟 𝓓 T] [ArithmeticalCompleteness α 𝔟 𝓓 T] : ProvabilityLogic α 𝔟 𝓓 T where
  is := by
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      simp only [Set.mem_setOf_eq];
      exact ArithmeticalSoundness.sound hp;
    . intro p hp;
      simp at hp;
      exact ArithmeticalCompleteness.complete hp;

end
-/

section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [DecidableEq (Sentence L)]
         (T₀ T : FirstOrder.Theory L) [T₀ ≼ T] [Diagonalization T₀]
         {𝔟 : ProvabilityPredicate L L}

lemma arithmetical_soundness_GL [𝔟.HBL T₀ T] (h : 𝐆𝐋 ⊢! p) : ∀ {f : realization L α}, T ⊢!. (f[𝔟] p) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift (T₀ := T₀);
    . exact FLT_shift (T₀ := T₀);
  | hNec ihp =>
    exact D1_shift (T₀ := T₀) ihp;
  | hMdp ihpq ihp =>
    simp [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [interpretation]; trivial;

lemma arithmetical_soundness_N [𝔟.HBL T₀ T] (h : 𝐍 ⊢! p) : ∀ {f : realization L α}, T ⊢!. (f[𝔟] p) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => simp at hp;
  | hNec ihp =>
    exact D1_shift (T₀ := T₀) ihp;
  | hMdp ihpq ihp =>
    simp only [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [interpretation]; trivial;

end ArithmeticalSoundness

end LO.ProvabilityLogic
