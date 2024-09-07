import Mathlib.Data.Finite.Card
import Incompleteness.ProvabilityLogic.Basic
import Logic.Modal.Kripke.GL.Tree

variable {α : Type u}

namespace LO.Kripke

namespace FiniteTransitiveTree

variable {F : FiniteTransitiveTree}

noncomputable def size (F : FiniteTransitiveTree) : ℕ := Nat.card F.World

@[simp] lemma size_le_0 : 0 < F.size := Finite.card_pos

def world_selector (F : FiniteTransitiveTree) : Fin F.size → F.World := by sorry

lemma world_selector.bijective : (Function.Bijective F.world_selector) := by sorry

lemma world_selector.zero : F.world_selector ⟨0, by simp⟩ = F.root := by sorry;


noncomputable def get_world (F : FiniteTransitiveTree) (i : Fin F.size) : F.World := F.world_selector i

lemma get_world_zero_root : F.get_world ⟨0, by simp⟩ = F.root := world_selector.zero

noncomputable def get_index (F : FiniteTransitiveTree) (w : F.World) : Fin F.size := world_selector.bijective.2 w |>.choose

lemma get_index_get_world : F.get_index (F.get_world i) = i := by sorry;

set_option pp.proofs true in
@[simp]
lemma get_world_get_index : F.get_world (F.get_index wi) = wi := by
  simp [get_world, get_index];
  sorry;

end FiniteTransitiveTree


namespace FiniteTransitiveTreeModel

noncomputable abbrev size (M : FiniteTransitiveTreeModel α) : ℕ := M.Tree.size

noncomputable abbrev get_world (M : FiniteTransitiveTreeModel α) (n : Fin M.size) : M.World := M.Tree.get_world n

noncomputable abbrev get_index (M : FiniteTransitiveTreeModel α) (w : M.World) : Fin M.size := M.Tree.get_index w

end FiniteTransitiveTreeModel

end LO.Kripke


namespace LO.System

open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [System F S]
         {𝓢 : S} [System.Classical 𝓢]
         {p q r : F}
         {Γ Δ : List F}

lemma conj_disj_demorgan₂'! (h : 𝓢 ⊢! ⋀Γ.map (~·)) : 𝓢 ⊢! ~⋁Γ := by sorry;

lemma conj_disj_demorgan₂_suppl'! (h : 𝓢 ⊢! p ⟶ ⋀Γ.map (~·)) : 𝓢 ⊢! p ⟶ ~⋁Γ :=
  deduct'! $ conj_disj_demorgan₂'! $ (of'! h) ⨀ by_axm!

lemma disj_mem (h : p ∈ Γ) : 𝓢 ⊢! p ⟶ ⋁Γ := by sorry;

lemma not_imply_prem''! (hpq : 𝓢 ⊢! p ⟶ q) (hpnr : 𝓢 ⊢! p ⟶ ~(r)) : 𝓢 ⊢! p ⟶ ~(q ⟶ r) :=
  deduct'! $ (contra₀'! $ not_or_of_imply!) ⨀ (demorgan₂'! $ and₃'! (dni'! $ of'! hpq ⨀ (by_axm!)) (of'! hpnr ⨀ (by_axm!)))

end LO.System


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

@[simp] lemma ln_zero : 0 < Φ.length := by rw [length, Φ.eq_length_model_size]; simp;

lemma _root_.Nat.lt_succ_sub {i : ℕ} (hi : i ≠ 0) : i < n + 1 → i - 1 < n := by induction i <;> simp_all;

lemma ln_M_size {i : Fin Φ.length} (hi : i ≠ ⟨0, ln_zero⟩ := by assumption) : i - 1 < M.size := by
  have := i.2; simp at this;
  exact Nat.lt_succ_sub ((Fin.ne_iff_vne i ⟨0, by simp⟩).mp hi) this;

noncomputable def realization (Φ : SolovaySentences 𝔅 M) : Realization α ℒₒᵣ := λ a =>
  let Φ' := List.finRange Φ.length
    |>.filter (λ i =>
      if hi : i = ⟨0, ln_zero⟩ then false
      else
        let wi : M.World := M.get_world ⟨i.1 - 1, ln_M_size⟩
        wi ⊧ a
    )
    |>.map (λ i => Φ.Φ[i]);
  ⋁Φ'

open LO.System LO.System.FiniteContext
open LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate
open Modal.Formula.Kripke

variable [System.Classical T]

#check List.mem_map


lemma lemma3
  (Φ : SolovaySentences 𝔅 M)
  (i : Fin Φ.length) (hi : i ≠ ⟨0, by simp⟩)
  (p : Modal.Formula α) :
  let wi : M.World := M.get_world ⟨i.1 - 1, ln_M_size hi⟩
  (wi ⊧ p → T ⊢!. Φ.Φ[i] ⟶ (Φ.realization.interpret 𝔅 p)) ∧ (¬(wi ⊧ p) → T ⊢!. Φ.Φ[i] ⟶ ~(Φ.realization.interpret 𝔅 p))
   := by
   simp only;
   induction p using Modal.Formula.rec' generalizing i with
    | hatom a =>
      simp only [Realization.interpret, SolovaySentences.realization];
      constructor;
      . intro h;
        apply disj_mem;
        simp;
        use i;
        constructor;
        . apply List.mem_filter_of_mem;
          . simp only [List.mem_finRange];
          . simp_all;
        . rfl;
      . intro h;
        apply conj_disj_demorgan₂_suppl'!;
        have : T ⊢!. Φ.Φ[i] ⟶ ⋀(List.finRange Φ.length |>.filter (i ≠ ·) |>.map (λ j => ~Φ.Φ[j])) := by
          apply deduct'!;
          apply iff_provable_list_conj.mpr;
          intro q hq;
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq;
          exact deductInv'! $ Φ.S2 i j (by simpa using List.of_mem_filter hj);
        exact imp_trans''! this $ conjconj_subset! (by
          simp;
          intro j hj;
          use j;
          constructor;
          . apply List.mem_filter_of_mem;
            . simp only [List.mem_finRange];
            . have := List.of_mem_filter hj;
              simp; by_contra hC; subst hC;
              simp_all;
          . rfl;
        )
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
        have hp := ihp i hi |>.1 hp;
        have hq := ihq i hi |>.2 hq;
        exact not_imply_prem''! hp hq;
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
        have : T ⊢!. Φ.Φ[↑j + 1] ⟶ ~Φ.realization.interpret 𝔅 p := ihp ⟨j.1 + 1, by simp⟩ (by simp) |>.2 (by convert hwj'; simp [j]);
        have h₁ := 𝔅.prov_distribute_imply $ contra₁'! this;
        have h₂ := Φ.S4 i hi ⟨j.1 + 1, by simp⟩ (by simp) (by convert hwj; simp [j]);
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
  -- (h₂ : ¬(Satisfies M.SimpleExtension M.root p))
  (h₃ : T ⊢!. Φ.realization.interpret 𝔅 p)
  : T ⊢!. Φ.Φ[1] ⟶ ~(Φ.realization.interpret 𝔅 p) := by
  let M' : Kripke.FiniteTransitiveTreeModel α := M↧;
  sorry;

  /-
  have : ¬(M↧.root) ⊧ p := by sorry;
  have : T ⊢!. Φ.Φ[1] ⟶ ~(Φ.realization.interpret 𝔅 p) := lemma4 h₁;
  have := contra₁'! this ⨀ h₂;
  have := 𝔅.D1 this;
  sorry;
  -/
  -- have := Φ.S4 ⟨1, by sorry⟩ (by simp) ⟨1, by sorry⟩ (by simp) (by sorry) ⨀ this;

end

end LO.ProvabilityLogic
