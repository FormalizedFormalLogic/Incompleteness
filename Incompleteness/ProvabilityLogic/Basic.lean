import Incompleteness.Arith.DC
import Incompleteness.DC.Basic
import Foundation.Modal.Hilbert.Systems

namespace LO

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal
open LO.Modal.Hilbert

variable {α : Type u}
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T U : Theory L}


namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
def Realization (α L) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def Realization.interpret
  {T U : FirstOrder.Theory L}
  (f : Realization α L) (𝔅 : ProvabilityPredicate T U) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | □φ => 𝔅 (f.interpret 𝔅 φ)
  | ⊥ => ⊥
  | φ ➝ ψ => (f.interpret 𝔅 φ) ➝ (f.interpret 𝔅 ψ)

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class ArithmeticalSound (Λ : Hilbert α) (𝔅 : ProvabilityPredicate T U) where
  sound : ∀ {φ}, (Λ ⊢! φ) → (∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ))

class ArithmeticalComplete (Λ : Hilbert α) (𝔅 : ProvabilityPredicate T U) where
  complete : ∀ {φ}, (∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ)) → (Λ ⊢! φ)

end LO.ProvabilityLogic
