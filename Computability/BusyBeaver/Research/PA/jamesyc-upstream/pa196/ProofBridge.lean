module
public import PAProof
public import FoundationBridge
public import Foundation.FirstOrder.LK.Simplified
@[expose] public section
namespace PalomarPA
attribute [local instance] calculusFormulaEq
open FFL FFL.FirstOrder

@[simp] theorem Formula.to_embed (p : Sentence) :
    p.embed.toFoundation = Rewriting.emb p.toFoundation := by
  rw [embed,to_rewrite]
  change Semiformula.rewAux _ _ = Semiformula.rewAux _ _
  congr 1
  apply Rew.ext
  · intro i; rfl
  · intro x; exact Empty.elim x
@[simp] theorem Formula.to_shift (p : Formula Nat n) :
    p.shift.toFoundation = Rewriting.shift p.toFoundation := by
  rw [shift,to_rewrite]
  rfl
@[simp] theorem Formula.to_free (p : Formula Nat 1) :
    p.free.toFoundation = Rewriting.free p.toFoundation := by
  rw [free,to_rewrite]
  change Semiformula.rewAux _ _ = Semiformula.rewAux _ _
  congr 1
  apply Rew.ext
  · intro i; fin_cases i; rfl
  · intro x; rfl
@[simp] theorem Formula.to_instantiate (p : Formula ξ 1) (t : Term ξ 0) :
    (p.instantiate t).toFoundation = p.toFoundation/[t.toFoundation] := by
  rw [instantiate,to_rewrite]
  change Semiformula.rewAux _ _ = Semiformula.rewAux _ _
  congr 1
  apply Rew.ext
  · intro i; fin_cases i; rfl
  · intro x; rfl

noncomputable def Derivation.toFoundation {T : Sentence → Prop} {S : Theory ℒₒᵣ}
    (hT : ∀ p, T p → p.toFoundation ∈ S) {Γ : Sequent}
    (d : Derivation T Γ) : LK2.Derivation S (Γ.image Formula.toFoundation) := by
  classical
  induction d with
  | closed Γ p hp hn =>
    apply LK2.Derivation.closed _ p.toFoundation
    · exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    · exact Finset.mem_image.mpr ⟨p.neg,hn,Formula.to_neg p⟩
  | «axiom» p ht hm =>
    apply LK2.Derivation.axm p.toFoundation (hT p ht)
    exact Finset.mem_image.mpr ⟨p.embed,hm,Formula.to_embed p⟩
  | top hm =>
    exact LK2.Derivation.verum (L := ℒₒᵣ) (T := S) (Finset.mem_image.mpr ⟨Formula.top,hm,rfl⟩)
  | and hm dp dq ihp ihq =>
    apply LK2.Derivation.and (L := ℒₒᵣ) (T := S) (Finset.mem_image.mpr ⟨_,hm,rfl⟩)
    · simpa using ihp
    · simpa using ihq
  | or hm dpq ih =>
    apply LK2.Derivation.or (L := ℒₒᵣ) (T := S) (Finset.mem_image.mpr ⟨_,hm,rfl⟩)
    simpa using ih
  | all hm dp ih =>
    apply LK2.Derivation.all (L := ℒₒᵣ) (T := S) (Finset.mem_image.mpr ⟨_,hm,rfl⟩)
    simpa [Finset.image_image,Function.comp_def] using ih
  | ex hm t dp ih =>
    apply LK2.Derivation.exs (L := ℒₒᵣ) (T := S) (Finset.mem_image.mpr ⟨_,hm,rfl⟩) t.toFoundation
    simpa using ih
  | weaken dp hs ih =>
    exact LK2.Derivation.wk (L := ℒₒᵣ) (T := S) ih (Finset.image_mono Formula.toFoundation hs)
  | shift dp ih =>
    simpa [Finset.image_image,Function.comp_def] using LK2.Derivation.shift ih
  | cut dp dn ihp ihn =>
    apply LK2.Derivation.cut
    · simpa using ihp
    · simpa [Semiformula.neg_eq] using ihn
theorem Formula.to_injective : Function.Injective (Formula.toFoundation (ξ := ξ) (n := n)) := by
  intro p q h
  have := congrArg Formula.fromFoundation h
  simpa using this

@[simp] theorem Formula.from_neg (p : Semiformula ℒₒᵣ ξ n) :
    fromFoundation (∼p) = (fromFoundation p).neg := by
  apply to_injective
  simp [Semiformula.neg_eq]
@[simp] theorem Formula.from_embed (p : FFL.FirstOrder.Sentence ℒₒᵣ) :
    Formula.fromFoundation (Rewriting.emb p : Proposition ℒₒᵣ) = (Formula.fromFoundation p).embed := by
  apply to_injective
  simp
@[simp] theorem Formula.from_shift (p : Semiproposition ℒₒᵣ n) :
    Formula.fromFoundation (Rewriting.shift p) = (Formula.fromFoundation p).shift := by
  apply to_injective
  simp
@[simp] theorem Formula.from_free (p : Semiproposition ℒₒᵣ 1) :
    Formula.fromFoundation (Rewriting.free p) = (Formula.fromFoundation p).free := by
  apply to_injective
  simp
@[simp] theorem Formula.from_instantiate (p : Semiformula ℒₒᵣ ξ 1) (t : Semiterm ℒₒᵣ ξ 0) :
    Formula.fromFoundation (p/[t]) = (Formula.fromFoundation p).instantiate (Term.fromFoundation t) := by
  apply to_injective
  simp

noncomputable def Derivation.fromFoundation {T : PalomarPA.Sentence → Prop} {S : Theory ℒₒᵣ}
    (hT : ∀ p, p ∈ S → T (Formula.fromFoundation p)) {Γ : Finset (Proposition ℒₒᵣ)}
    (d : LK2.Derivation S Γ) : Derivation T (Γ.image Formula.fromFoundation) := by
  classical
  induction d with
  | closed Γ p hp hn =>
    apply Derivation.closed _ (Formula.fromFoundation p)
    · exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    · exact Finset.mem_image.mpr ⟨∼p,hn,Formula.from_neg p⟩
  | axm p ht hm =>
    apply Derivation.axiom (Formula.fromFoundation p) (hT p ht)
    exact Finset.mem_image.mpr ⟨Rewriting.emb p,hm,Formula.from_embed p⟩
  | verum hm =>
    exact Derivation.top (Finset.mem_image.mpr ⟨⊤,hm,rfl⟩)
  | and hm dp dq ihp ihq =>
    apply Derivation.and (Finset.mem_image.mpr ⟨_,hm,rfl⟩)
    · simpa using ihp
    · simpa using ihq
  | or hm dpq ih =>
    apply Derivation.or (Finset.mem_image.mpr ⟨_,hm,rfl⟩)
    simpa using ih
  | all hm dp ih =>
    apply Derivation.all (Finset.mem_image.mpr ⟨_,hm,rfl⟩)
    simpa [Finset.image_image,Function.comp_def] using ih
  | exs hm t dp ih =>
    apply Derivation.ex (Finset.mem_image.mpr ⟨_,hm,rfl⟩) (Term.fromFoundation t)
    simpa using ih
  | wk dp hs ih =>
    exact Derivation.weaken ih (Finset.image_mono Formula.fromFoundation hs)
  | shift dp ih =>
    simpa [Finset.image_image,Function.comp_def] using Derivation.shift ih
  | cut dp dn ihp ihn =>
    apply Derivation.cut
    · simpa using ihp
    · simpa using ihn

theorem provable_iff {T : PalomarPA.Sentence → Prop} {S : Theory ℒₒᵣ}
    (hT : ∀ p, T p ↔ p.toFoundation ∈ S) (p : PalomarPA.Sentence) :
    Provable T p ↔ S ⊢ p.toFoundation := by
  rw [provable_iff_derivable2 (L := ℒₒᵣ) (T := S)]
  constructor
  · rintro ⟨d⟩
    have e := d.toFoundation (fun q h => (hT q).mp h)
    exact ⟨by simpa using e⟩
  · rintro ⟨d⟩
    have e := Derivation.fromFoundation (T := T) (fun q h =>
      (hT (Formula.fromFoundation q)).mpr (by simpa using h)) d
    exact ⟨by simpa using e⟩

#print axioms provable_iff
#print axioms Derivation.fromFoundation
#print axioms Derivation.toFoundation
end PalomarPA
