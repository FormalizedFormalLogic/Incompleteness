import Incompleteness.ProvabilityLogic.GL.Preface

namespace LO.ProvabilityLogic

open Classical

open System System.FiniteContext
open Modal
open Modal.Formula
open Modal.Formula.Kripke
open Modal.Kripke
open FirstOrder.DerivabilityCondition
open FirstOrder.DerivabilityCondition.ProvabilityPredicate

variable {T U : FirstOrder.Theory ℒₒᵣ} {𝔅 : ProvabilityPredicate T T} [𝔅.HBL]
variable {M : FiniteTransitiveTreeModel}

structure SolovaySentences
  {T U : FirstOrder.Theory ℒₒᵣ}
  (𝔅 : ProvabilityPredicate T U) [𝔅.HBL]
  (M : FiniteTransitiveTreeModel)
  where
    Φ : List (FirstOrder.Sentence ℒₒᵣ)
    eq_length_model_size : Φ.length = M.size + 1
    S1 : T ⊢!. ⋁Φ
    S2 : ∀ i : Fin Φ.length, ∀ j : Fin Φ.length, i ≠ j → T ⊢!. Φ[i] ➝ ∼Φ[j]
    S3 :
      ∀ i : Fin Φ.length, (hi : i ≠ ⟨0, by omega⟩) →
      letI Φ' := List.finRange Φ.length
        |>.filter (λ j =>
            letI wi : M.World := M.get_world ⟨i.1 - 1, by omega⟩
            letI wj : M.World := M.get_world ⟨j.1 - 1, by omega⟩
            wi ≺ wj
          )
        |>.map (λ j => Φ[j]);
      T ⊢!. Φ[i] ➝ 𝔅 (⋁Φ')
    S4 :
      ∀ i : Fin Φ.length,
      ∀ j : Fin Φ.length, (hj : j ≠ ⟨0, by omega⟩) →
      letI wi : M.World := M.get_world ⟨i.1 - 1, by omega⟩;
      letI wj : M.World := M.get_world ⟨j.1 - 1, by omega⟩;
      wi ≺ wj →
      T ⊢!. 𝔅 (∼Φ[j]) ➝ ∼Φ[i]

namespace SolovaySentences

-- instance : CoeSort (SolovaySentences M 𝔅) (List (Sentence ℒₒᵣ)) := ⟨λ Φ => Φ.Φ⟩

attribute [simp] eq_length_model_size

variable {Φ : SolovaySentences 𝔅 M}

abbrev length (Φ : SolovaySentences 𝔅 M) : ℕ := Φ.Φ.length

@[simp]
lemma ln_zero : 0 < Φ.length := by
  rw [length, Φ.eq_length_model_size];
  simp;

lemma ln_M_size {i : Fin Φ.length} (hi : i ≠ ⟨0, ln_zero⟩ := by assumption) : i - 1 < M.size := by
  have := i.2;
  simp only [eq_length_model_size] at this;
  exact Nat.lt_succ_sub ((Fin.ne_iff_vne i ⟨0, by simp⟩).mp hi) this;

noncomputable def realization (Φ : SolovaySentences 𝔅 M) : Realization ℕ ℒₒᵣ := λ a =>
  letI Φ' := List.finRange Φ.length
    |>.filter (λ i =>
      if hi : i = ⟨0, ln_zero⟩ then False
      else Kripke.Satisfies M.toModel (M.get_world ⟨i.1 - 1, ln_M_size⟩) a
    )
    |>.map (λ i => Φ.Φ[i]);
  ⋁Φ'


lemma lemma1
  (Φ : SolovaySentences 𝔅 M) (i : Fin Φ.length) (hi : i ≠ ⟨0, by simp⟩)
  (A : Modal.Formula ℕ) :
  let wi : M.World := M.get_world ⟨i - 1, SolovaySentences.ln_M_size hi⟩
  (wi ⊧ A → T ⊢!. Φ.Φ[i] ➝ (Φ.realization.interpret 𝔅 A)) ∧ (¬(wi ⊧ A) → T ⊢!. Φ.Φ[i] ➝ ∼(Φ.realization.interpret 𝔅 A))
   := by
   intro wi;
   induction A using Modal.Formula.rec' generalizing i with
    | hfalsum => simp [Realization.interpret, Semantics.Realize, Satisfies];
    | hatom a =>
      simp only [Realization.interpret, SolovaySentences.realization];
      constructor;
      . intro h;
        apply disj_mem!;
        simp;
        use i;
        constructor;
        . split;
          . contradiction;
          . simpa;
        . rfl;
      . intro h;
        apply conj_disj_demorgan₂_suppl'!;
        have : T ⊢!. Φ.Φ[i] ➝ ⋀(List.finRange Φ.length |>.filter (i ≠ ·) |>.map (λ j => ∼Φ.Φ[j])) := by
          apply deduct'!;
          apply iff_provable_list_conj.mpr;
          intro q hq;
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq;
          exact deductInv'! $ Φ.S2 i j (by simpa using List.of_mem_filter hj);
        exact imp_trans''! this $ conjconj_subset! $ by
          simp;
          intro j hj;
          use j;
          constructor;
          . rintro rfl;
            have : wi ⊧ (atom a) := by simpa [hi] using hj;
            contradiction;
          . rfl;
    | himp A B ihA ihB =>
      simp only [Realization.interpret];
      constructor;
      . intro h;
        rcases (not_or_of_imp $ Satisfies.imp_def.mp h) with (hp | hq);
        . apply deduct'!;
          exact efq_imply_not₁! ⨀ (deductInv'! $ ihA i hi |>.2 hp)
        . apply deduct'!;
          exact imply₁'! $ deductInv'! $ ihB i hi |>.1 hq;
      . intro h;
        have := Satisfies.imp_def.not.mp h; push_neg at this;
        replace ⟨hp, hq⟩ := this;
        have hp := ihA i hi |>.1 hp;
        have hq := ihB i hi |>.2 hq;
        exact not_imply_prem''! hp hq;
    | hbox A ihA =>
      simp only [Realization.interpret];
      constructor;
      . intro h;
        apply imp_trans''! (Φ.S3 i hi) ?_;
        apply prov_distribute_imply;
        apply disj_intro;
        intro j hj;
        simp at hj;
        obtain ⟨j, ⟨hj₂, rfl⟩⟩ := hj;
        apply ihA j (by rintro rfl; simp at hj₂) |>.1;
        apply h;
        exact hj₂;
      . intro h;
        have := Satisfies.box_def.not.mp h; push_neg at this;
        obtain ⟨wj, hwj, hwj'⟩ := this;
        let j := M.get_index wj;
        have : T ⊢!. Φ.Φ[↑j + 1] ➝ ∼Φ.realization.interpret 𝔅 A := ihA ⟨j.1 + 1, by simp⟩ (by simp) |>.2 (by convert hwj'; simp [j]);
        have h₁ := 𝔅.prov_distribute_imply $ contra₁'! this;
        have h₂ := Φ.S4 i ⟨j.1 + 1, by simp⟩ (by simp) (by convert hwj; simp [j]);
        exact contra₁'! $ imp_trans''! h₁ h₂;

lemma lemma2 {Φ : SolovaySentences 𝔅 M} (h : ¬M.root ⊧ A) : T ⊢!. Φ.Φ[1] ➝ ∼(Φ.realization.interpret 𝔅 A) := by
  apply lemma1 Φ ⟨1, by simp⟩ (by simp) A |>.2;
  convert h;
  exact FiniteTransitiveTree.get_world_zero_root;

lemma lemma3 [Consistent T] (Φ : SolovaySentences 𝔅 M↧) (h : ¬M.root ⊧ A) : T ⊬. Φ.realization.interpret 𝔅 A := by
  by_contra hC;
  suffices T ⊢!. ⊥ by
    have : ¬Consistent T := consistent_iff_unprovable_bot.not.mpr $ by simpa using this;
    contradiction;

  have : T ⊢!. Φ.Φ[1] ➝ ∼Φ.realization.interpret 𝔅 A := lemma2 $ by
    have := @FiniteTransitiveTreeModel.SimpleExtension.modal_equivalence_original_world M M.root A |>.not.mp h;
    suffices ¬(Satisfies  M↧.toModel (Sum.inr M.root) A) by sorry;
    exact this;
  have : T ⊢!. ∼Φ.Φ[1] := contra₁'! this ⨀ hC;
  have : T ⊢!. (𝔅 (∼Φ.Φ[1])) := D1_shift this;
  have : T ⊢!. ∼Φ.Φ[0] := Φ.S4 ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp) (by sorry) ⨀ this;
  sorry;

end SolovaySentences


noncomputable def _root_.LO.Modal.Kripke.FiniteTransitiveTreeModel.solovaySentences (M : FiniteTransitiveTreeModel) (𝔅 : ProvabilityPredicate T T) [𝔅.HBL] : SolovaySentences 𝔅 M := by sorry;


end LO.ProvabilityLogic
