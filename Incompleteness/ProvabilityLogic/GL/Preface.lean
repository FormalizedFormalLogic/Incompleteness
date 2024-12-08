import Foundation.Modal.Kripke.GL.Tree
import Incompleteness.ProvabilityLogic.Basic
import Mathlib.Data.Finite.Card


section

lemma _root_.Nat.lt_succ_sub {i : ℕ} (hi : i ≠ 0) : i < n + 1 → i - 1 < n := by induction i <;> simp_all;

end


namespace LO.System

open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [System F S]
         {𝓢 : S} [System.Classical 𝓢]
         {p q r : F}
         {Γ Δ : List F}

lemma conj_disj_demorgan₂'! (h : 𝓢 ⊢! ⋀Γ.map (∼·)) : 𝓢 ⊢! ∼⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q => simp_all;
  | hcons q Γ hΓ ih =>
    replace h : 𝓢 ⊢! ∼q ⋏ (⋀Γ.map (∼·)) := by
      have e := List.conj₂_cons_nonempty (a := ∼q) (as := Γ.map (∼·)) (by simpa using hΓ);
      simpa [←e] using h;
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    apply demorgan₂'!;
    apply and₃'!;
    . exact and₁'! h;
    . exact ih $ and₂'! h

lemma conj_disj_demorgan₂_suppl'! (h : 𝓢 ⊢! p ➝ ⋀Γ.map (∼·)) : 𝓢 ⊢! p ➝ ∼⋁Γ :=
  deduct'! $ conj_disj_demorgan₂'! $ (of'! h) ⨀ by_axm!

omit [DecidableEq F] in
lemma disj_mem! (h : p ∈ Γ) : 𝓢 ⊢! p ➝ ⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp at h;
  | hsingle q =>
    replace h : p = q := by simpa using h;
    subst h;
    simp;
  | hcons q Γ hΓ ih =>
    replace h : p = q ∨ p ∈ Γ := by simpa using h;
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    rcases h with (rfl | h);
    . exact or₁!;
    . exact imply_right_or'! $ ih h

lemma not_imply_prem''! (hpq : 𝓢 ⊢! p ➝ q) (hpnr : 𝓢 ⊢! p ➝ ∼(r)) : 𝓢 ⊢! p ➝ ∼(q ➝ r) :=
  deduct'! $ (contra₀'! $ not_or_of_imply!) ⨀ (demorgan₂'! $ and₃'! (dni'! $ of'! hpq ⨀ (by_axm!)) (of'! hpnr ⨀ (by_axm!)))

lemma disj_intro (h : ∀ q ∈ Γ, 𝓢 ⊢! q ➝ p) : 𝓢 ⊢! ⋁Γ ➝ p := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q => simp_all;
  | hcons q Γ hΓ ih =>
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    obtain ⟨h₁, h₂⟩ := by simpa using h;
    replace h₂ := ih h₂;
    exact or₃''! h₁ h₂;

end LO.System



namespace LO.Modal.Kripke

open Modal.Formula.Kripke

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

@[simp]
lemma cannotback_zero : ¬(x ≺ F.get_world ⟨0, by simp⟩) := by
  rw [get_world_zero_root];
  sorry;

end FiniteTransitiveTree


instance {M : FiniteTransitiveTreeModel} : Semantics (Modal.Formula ℕ) (M.World) := ⟨λ b a => Satisfies M.toModel b a⟩


end LO.Modal.Kripke
