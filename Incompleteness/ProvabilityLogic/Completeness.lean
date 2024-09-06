import Mathlib.Data.Finite.Card
import Incompleteness.ProvabilityLogic.Basic
import Logic.Modal.Kripke.GL.Tree

variable {α : Type u}

namespace LO.Kripke

structure SyntacticalFiniteTransitiveTree extends FiniteTransitiveTree where
  World_nat : World = ℕ

namespace SyntacticalFiniteTransitiveTree

end SyntacticalFiniteTransitiveTree



#check FiniteFrame

namespace FiniteTransitiveTree

variable {F : FiniteTransitiveTree}

noncomputable def size (F : FiniteTransitiveTree) : ℕ := Nat.card F.World

@[simp] lemma size_le_0 : 0 < F.size := Finite.card_pos

lemma exists_bijection : ∃ f : Fin F.size → F.World, (Function.Bijective f ∧ f ⟨0, by simp⟩ = F.root) := by sorry


noncomputable def get_world (F : FiniteTransitiveTree) (i : Fin F.size) : F.World := exists_bijection.choose i

lemma get_world_zero_root : F.get_world ⟨0, by simp⟩ = F.root := exists_bijection.choose_spec.2

noncomputable def get_index (F : FiniteTransitiveTree) (w : F.World) : Fin F.size := exists_bijection.choose_spec.1.2 w |>.choose

end FiniteTransitiveTree


namespace FiniteTransitiveTreeModel

noncomputable abbrev size (M : FiniteTransitiveTreeModel α) : ℕ := M.Tree.size

noncomputable abbrev get_world (M : FiniteTransitiveTreeModel α) (n : Fin M.size) : M.World := M.Tree.get_world n

noncomputable abbrev get_index (M : FiniteTransitiveTreeModel α) (w : M.World) : Fin M.size := M.Tree.get_index w

end FiniteTransitiveTreeModel


end LO.Kripke


namespace LO.ProvabilityLogic

open Classical

open LO.FirstOrder.DerivabilityCondition (ProvabilityPredicate)

structure SolovaySentences
  {T U : FirstOrder.Theory ℒₒᵣ}
  (𝔅 : ProvabilityPredicate T U)
  (M : Kripke.FiniteTransitiveTreeModel α)
  where
    Φ : List (FirstOrder.Sentence ℒₒᵣ)
    eq_length_model_size : Φ.length = M.size + 1
    S1 : T ⊢!. ⋀Φ
    S2 : ∀ i : Fin Φ.length, ∀ j : Fin Φ.length, i ≠ j → T ⊢!. Φ[i] ⟶ ~Φ[j]
    S3 :
      ∀ i : Fin Φ.length, (hi : i ≠ ⟨0, by omega⟩) →
      let Φ' := List.finRange Φ.length
        |>.filter (λ j =>
            let wi : M.World := M.get_world ⟨i.1 - 1, by omega⟩
            let wj : M.World := M.get_world ⟨j.1 - 1, by omega⟩
            wi ≺ wj
          )
        |>.map (λ j => Φ[j]);
      T ⊢!. Φ[i] ⟶ 𝔅 (⋁Φ')
    S4 :
      ∀ i : Fin Φ.length, (hi : i ≠ ⟨0, by omega⟩) →
      ∀ j : Fin Φ.length, (hj : j ≠ ⟨0, by omega⟩) →
      let wi : M.World := M.get_world ⟨i.1 - 1, by omega⟩;
      let wj : M.World := M.get_world ⟨j.1 - 1, by omega⟩;
      wi ≺ wj →
      T ⊢!. 𝔅 (~Φ[j]) ⟶ ~Φ[i]

namespace SolovaySentences

instance : CoeSort (SolovaySentences M 𝔅) (List (FirstOrder.Sentence ℒₒᵣ)) := ⟨λ Φ => Φ.Φ⟩

attribute [simp] eq_length_model_size

variable
  {T U : FirstOrder.Theory ℒₒᵣ} {𝔅 : ProvabilityPredicate T T} [𝔅.HBL]
  {M : Kripke.FiniteTransitiveTreeModel α}
  {Φ : SolovaySentences 𝔅 M}

abbrev length (Φ : SolovaySentences 𝔅 M) : ℕ := Φ.Φ.length

@[simp] lemma ln_zero : Φ.length > 0 := by rw [length, Φ.eq_length_model_size]; simp;

noncomputable def realization (Φ : SolovaySentences 𝔅 M) : Realization α ℒₒᵣ := λ a =>
  let Φ' := List.finRange Φ.length
    |>.filter (λ i =>
      let wi : M.World := M.get_world ⟨i.1 - 1, by
        have := i.2;
        have := Φ.eq_length_model_size;
        sorry;
      ⟩
      wi ⊧ a
    )
    |>.map (λ i => Φ.Φ[i]);
  ⋁Φ'

open LO.System LO.System.FiniteContext
open LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate
open Modal.Formula.Kripke

variable [System.Classical T]

lemma lemma3
  (Φ : SolovaySentences 𝔅 M)
  (i : Fin Φ.length) (hi : i ≠ ⟨0, by simp⟩)
  (p : Modal.Formula α) :
  let wi : M.World := M.get_world ⟨i.1 - 1, by sorry⟩
  (wi ⊧ p → T ⊢!. Φ.Φ[i] ⟶ (Φ.realization.interpret 𝔅 p)) ∧ (¬(wi ⊧ p) → T ⊢!. Φ.Φ[i] ⟶ ~(Φ.realization.interpret 𝔅 p))
   := by
   simp only;
   induction p using Modal.Formula.rec' generalizing i with
    | hatom a =>
      simp only [Realization.interpret, SolovaySentences.realization];
      constructor;
      . intro h;
        sorry;
      . intro h;
        sorry;
    | himp p q ihp ihq =>
      simp only [Realization.interpret];
      constructor;
      . intro h;
        rcases (not_or_of_imp $ Satisfies.imp_def.mp h) with (hp | hq);
        . apply deduct'!;
          exact efq_imply_not₁! ⨀ (deductInv'! $ ihp i hi |>.2 hp)
        . apply deduct'!;
          exact dhyp! $ deductInv'! $ ihq i hi |>.1 hq;
      . intro h;
        have := Satisfies.imp_def.not.mp h; push_neg at this;
        replace ⟨hp, hq⟩ := this;
        have := ihp i hi |>.1 hp;
        have := ihq i hi |>.2 hq;
        apply deduct'!;
        sorry;
    | hfalsum =>
      simp only [
        Semantics.Realize, Satisfies, Fin.getElem_fin, Realization.interpret, false_implies, not_false_eq_true,
        DeMorgan.falsum, DeMorgan.neg, imply_left_verum, dne'!, imp_self, and_self
      ];
    | hbox p ihp =>
      simp only [Realization.interpret];
      constructor;
      . intro h;
        have := Satisfies.box_def.mp h;
        have := Φ.S3 i hi;
        sorry;
      . intro h;
        have := Satisfies.box_def.not.mp h; push_neg at this;
        obtain ⟨wj, hwj, hwj'⟩ := this;
        let j := M.get_index wj;
        have := ihp ⟨j.1 + 1, by sorry⟩ (by simp) |>.2 (by sorry);
        have h₁ := 𝔅.prov_distribute_imply $ contra₁'! this;
        have h₂ := Φ.S4 i (by sorry) ⟨j.1 + 1, by sorry⟩ (by sorry) (by sorry);
        exact contra₁'! $ imp_trans''! h₁ h₂;


end SolovaySentences


section

open LO.System LO.System.FiniteContext
open LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate
open Modal.Formula.Kripke

variable
  {T U : FirstOrder.Theory ℒₒᵣ} {𝔅 : ProvabilityPredicate T T} [𝔅.HBL]
  {M : Kripke.FiniteTransitiveTreeModel α}
  {Φ : SolovaySentences 𝔅 M}

lemma lemma4 (h : ¬M.root ⊧ p) : T ⊢!. Φ.Φ[1] ⟶ ~(Φ.realization.interpret 𝔅 p) := by
  apply SolovaySentences.lemma3 Φ ⟨1, by simp⟩ (by simp) p |>.2;
  convert h;
  exact Kripke.FiniteTransitiveTree.get_world_zero_root;

example
  (h₁ : ¬M.root ⊧ p)
  (h₂ : ¬M.root ⊧ p)
  (h₃ : T ⊢!. Φ.realization.interpret 𝔅 p)
  : T ⊢!. Φ.Φ[1] ⟶ ~(Φ.realization.interpret 𝔅 p) := by
  let M' : Kripke.FiniteTransitiveTreeModel α := M↧;

  have : ¬(M↧.root) ⊧ p := by sorry;
  have : T ⊢!. Φ.Φ[1] ⟶ ~(Φ.realization.interpret 𝔅 p) := lemma4 h₁;
  have := contra₁'! this ⨀ h₂;
  have := 𝔅.D1 this;
  sorry;
  -- have := Φ.S4 ⟨1, by sorry⟩ (by simp) ⟨1, by sorry⟩ (by simp) (by sorry) ⨀ this;

end

end LO.ProvabilityLogic
