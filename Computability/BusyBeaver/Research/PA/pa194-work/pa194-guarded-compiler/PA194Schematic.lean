import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
import Foundation.FirstOrder.Completeness.CounterModel
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Instantiating predicate letters of a standard derivation by internal formulas

`boxL ar` is a language without function symbols whose relation symbols are `m` predicate
letters of the arities `ar`. A standard formula of `boxL ar` and internal formulas
`σ 0, …, σ (m-1)` of a language `L`, of these arities, give an internal formula of `L`
(`inst σ φ`): the atom of the `i`-th letter at terms `v` becomes `σ i` at `v`. A standard
derivation in pure logic of a sequent of `boxL ar` gives an internal derivation of its
instance, for every choice of `σ`, including nonstandard formulas (`instDer`). With the
completeness theorem, a sentence of `boxL ar` that holds in every structure has all its
instances provable in every internal theory (`inst_provable_of_valid`).

Nothing here depends on the 194-state development.
-/
namespace PA194Schematic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Predicate letters: the `i`-th letter has arity `ar i`. -/
inductive BoxRel {m : ℕ} (ar : Fin m → ℕ) : ℕ → Type
  | box (i : Fin m) : BoxRel ar (ar i)

/-- The language of the predicate letters; it has no function symbol. -/
def boxL {m : ℕ} (ar : Fin m → ℕ) : Language where
  Func := fun _ => PEmpty
  Rel := BoxRel ar

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {m : ℕ} {ar : Fin m → ℕ}

/-- The internal term of a standard term of `boxL ar`; such a term is a variable. -/
noncomputable def tq {n : ℕ} : SyntacticSemiterm (boxL ar) n → Bootstrapping.Semiterm V L n
  | .bvar i => Bootstrapping.Semiterm.bvar i
  | .fvar x => Bootstrapping.Semiterm.fvar (x : V)
  | .func f _ => nomatch f

@[simp] theorem tq_bvar {n : ℕ} (i : Fin n) :
    (tq (.bvar i : SyntacticSemiterm (boxL ar) n) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.bvar i := rfl
@[simp] theorem tq_fvar {n : ℕ} (x : ℕ) :
    (tq (.fvar x : SyntacticSemiterm (boxL ar) n) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.fvar (x : V) := rfl

theorem tq_shift {n : ℕ} (t : SyntacticSemiterm (boxL ar) n) :
    (tq (Rew.shift t) : Bootstrapping.Semiterm V L n) = (tq t).shift := by
  cases t with
  | bvar i => simp
  | fvar x => simp
  | func f _ => exact nomatch f
theorem tq_bShift {n : ℕ} (t : SyntacticSemiterm (boxL ar) n) :
    (tq (Rew.bShift t) : Bootstrapping.Semiterm V L (n+1)) = (tq t).bShift := by
  cases t with
  | bvar i => simp
  | fvar x => simp
  | func f _ => exact nomatch f
theorem tq_substs {n k : ℕ} (w : Fin n → SyntacticSemiterm (boxL ar) k)
    (t : SyntacticSemiterm (boxL ar) n) :
    (tq (Rew.subst w t) : Bootstrapping.Semiterm V L k) = (tq t).subst (fun i => tq (w i)) := by
  cases t with
  | bvar i => simp
  | fvar x => simp
  | func f _ => exact nomatch f

/-- The instance of a standard formula of `boxL ar` at internal formulas `σ`. -/
noncomputable def inst (σ : (i : Fin m) → Bootstrapping.Semiformula V L (ar i)) :
    {n : ℕ} → Semiproposition (boxL ar) n → Bootstrapping.Semiformula V L n
  | _, .rel (.box i) v => (σ i).subst fun j => tq (v j)
  | _, .nrel (.box i) v => ∼((σ i).subst fun j => tq (v j))
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, φ ⋏ ψ => inst σ φ ⋏ inst σ ψ
  | _, φ ⋎ ψ => inst σ φ ⋎ inst σ ψ
  | _, ∀⁰ φ => ∀⁰ inst σ φ
  | _, ∃⁰ φ => ∃⁰ inst σ φ

variable (σ : (i : Fin m) → Bootstrapping.Semiformula V L (ar i))

@[simp] theorem inst_verum {n : ℕ} : inst σ (⊤ : Semiproposition (boxL ar) n) = ⊤ := by simp [inst]
@[simp] theorem inst_falsum {n : ℕ} : inst σ (⊥ : Semiproposition (boxL ar) n) = ⊥ := by simp [inst]
@[simp] theorem inst_and {n : ℕ} (φ ψ : Semiproposition (boxL ar) n) :
    inst σ (φ ⋏ ψ) = inst σ φ ⋏ inst σ ψ := by simp [inst]
@[simp] theorem inst_or {n : ℕ} (φ ψ : Semiproposition (boxL ar) n) :
    inst σ (φ ⋎ ψ) = inst σ φ ⋎ inst σ ψ := by simp [inst]
@[simp] theorem inst_all {n : ℕ} (φ : Semiproposition (boxL ar) (n+1)) :
    inst σ (∀⁰ φ) = ∀⁰ inst σ φ := by simp [inst]
@[simp] theorem inst_exs {n : ℕ} (φ : Semiproposition (boxL ar) (n+1)) :
    inst σ (∃⁰ φ) = ∃⁰ inst σ φ := by simp [inst]
@[simp] theorem inst_rel {n : ℕ} (i : Fin m) (v : Fin (ar i) → SyntacticSemiterm (boxL ar) n) :
    inst σ (FirstOrder.Semiformula.rel (L := boxL ar) (BoxRel.box i) v) =
      (σ i).subst fun j => tq (v j) := by simp [inst]
@[simp] theorem inst_nrel {n : ℕ} (i : Fin m) (v : Fin (ar i) → SyntacticSemiterm (boxL ar) n) :
    inst σ (FirstOrder.Semiformula.nrel (L := boxL ar) (BoxRel.box i) v) =
      ∼((σ i).subst fun j => tq (v j)) := by simp [inst]

theorem inst_nrel_eq {n k : ℕ} (r : (boxL ar).Rel k) (v : Fin k → SyntacticSemiterm (boxL ar) n) :
    inst σ (FirstOrder.Semiformula.nrel r v) = ∼(inst σ (FirstOrder.Semiformula.rel r v)) := by
  cases r with
  | box i => simp

theorem inst_neg {n : ℕ} (φ : Semiproposition (boxL ar) n) : inst σ (∼φ) = ∼(inst σ φ) := by
  induction φ using FirstOrder.Semiformula.rec'
  case hrel k r v => cases r; simp
  case hnrel k r v => cases r; simp
  case hverum => simp
  case hfalsum => simp
  case hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hall φ ih => simp [ih]
  case hexs φ ih => simp [ih]

theorem inst_imp {n : ℕ} (φ ψ : Semiproposition (boxL ar) n) :
    inst σ (φ 🡒 ψ) = inst σ φ 🡒 inst σ ψ := by
  simp [FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def, inst_neg]

/-- Shifting the instance shifts the letters and the formula. -/
theorem inst_shift {n : ℕ} (φ : Semiproposition (boxL ar) n) :
    inst (fun i => (σ i).shift) (Rewriting.shift φ) = (inst σ φ).shift := by
  induction φ using FirstOrder.Semiformula.rec'
  case hrel k r v =>
    cases r with
    | box i =>
      have e : (Rewriting.shift (FirstOrder.Semiformula.rel (L := boxL ar) (BoxRel.box i) v) :
          Semiproposition (boxL ar) _) =
          FirstOrder.Semiformula.rel (L := boxL ar) (BoxRel.box i) (fun j => Rew.shift (v j)) :=
        FirstOrder.Semiformula.rew_rel _ _ _
      rw [e, inst_rel, inst_rel, Bootstrapping.Semiformula.shift_substs]
      congr 1
      funext j
      simp [tq_shift]
  case hnrel k r v =>
    cases r with
    | box i =>
      have e : (Rewriting.shift (FirstOrder.Semiformula.nrel (L := boxL ar) (BoxRel.box i) v) :
          Semiproposition (boxL ar) _) =
          FirstOrder.Semiformula.nrel (L := boxL ar) (BoxRel.box i) (fun j => Rew.shift (v j)) :=
        FirstOrder.Semiformula.rew_nrel _ _ _
      rw [e, inst_nrel, inst_nrel, Bootstrapping.Semiformula.shift_neg,
        Bootstrapping.Semiformula.shift_substs]
      congr 2
      funext j
      simp [tq_shift]
  case hverum => simp
  case hfalsum => simp
  case hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hall φ ih => simp [ih]
  case hexs φ ih => simp [ih]

/-- The instance commutes with substitution of terms. -/
theorem inst_substs {n k : ℕ} (w : Fin n → SyntacticSemiterm (boxL ar) k)
    (φ : Semiproposition (boxL ar) n) :
    inst σ (φ ⇜ w) = (inst σ φ).subst (fun i => tq (w i)) := by
  induction φ using FirstOrder.Semiformula.rec' generalizing k
  case hrel a r v =>
    cases r with
    | box i =>
      have e : ((FirstOrder.Semiformula.rel (L := boxL ar) (BoxRel.box i) v) ⇜ w :
          Semiproposition (boxL ar) k) =
          FirstOrder.Semiformula.rel (L := boxL ar) (BoxRel.box i) (fun j => Rew.subst w (v j)) :=
        FirstOrder.Semiformula.rew_rel _ _ _
      rw [e, inst_rel, inst_rel, Bootstrapping.Semiformula.substs_substs]
      congr 1
      funext j
      simp [tq_substs]
  case hnrel a r v =>
    cases r with
    | box i =>
      have e : ((FirstOrder.Semiformula.nrel (L := boxL ar) (BoxRel.box i) v) ⇜ w :
          Semiproposition (boxL ar) k) =
          FirstOrder.Semiformula.nrel (L := boxL ar) (BoxRel.box i) (fun j => Rew.subst w (v j)) :=
        FirstOrder.Semiformula.rew_nrel _ _ _
      rw [e, inst_nrel, inst_nrel, Bootstrapping.Semiformula.substs_neg,
        Bootstrapping.Semiformula.substs_substs]
      congr 2
      funext j
      simp [tq_substs]
  case hverum => simp
  case hfalsum => simp
  case hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hall φ ih =>
    have e : ((∀⁰ φ) ⇜ w : Semiproposition (boxL ar) k) =
        ∀⁰ (φ ⇜ (#0 :> fun i => Rew.bShift (w i))) := by
      simp [Rew.q_subst]
      rfl
    rw [e, inst_all, inst_all, ih, Bootstrapping.Semiformula.substs_all]
    congr 2
    funext i
    cases i using Fin.cases <;> simp [tq_bShift]
  case hexs φ ih =>
    have e : ((∃⁰ φ) ⇜ w : Semiproposition (boxL ar) k) =
        ∃⁰ (φ ⇜ (#0 :> fun i => Rew.bShift (w i))) := by
      simp [Rew.q_subst]
      rfl
    rw [e, inst_exs, inst_exs, ih, Bootstrapping.Semiformula.substs_ex]
    congr 2
    funext i
    cases i using Fin.cases <;> simp [tq_bShift]

theorem inst_substs1 (t : SyntacticTerm (boxL ar)) (φ : Semiproposition (boxL ar) 1) :
    inst σ (φ/[t]) = (inst σ φ).subst ![tq t] := by
  rw [inst_substs]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp

/-- The instance of the opened formula is the opened instance at the shifted letters. -/
theorem inst_free (φ : Semiproposition (boxL ar) 1) :
    inst (fun i => (σ i).shift) (Rewriting.free φ) = (inst σ φ).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free, inst_substs1, inst_shift]
  simp [Bootstrapping.Semiformula.free]

/-! ### Sequents -/

/-- The instance of a standard sequent. -/
noncomputable def instSeq (σ : (i : Fin m) → Bootstrapping.Semiformula V L (ar i)) :
    FirstOrder.Sequent (boxL ar) → Bootstrapping.Sequent V L
  | [] => ∅
  | φ :: Γ => insert (inst σ φ) (instSeq σ Γ)

theorem mem_instSeq {Γ : FirstOrder.Sequent (boxL ar)} {ψ : Bootstrapping.Formula V L} :
    ψ ∈ instSeq σ Γ ↔ ∃ φ ∈ Γ, ψ = inst σ φ := by
  induction Γ with
  | nil => simp [instSeq]
  | cons φ Γ ih => simp [instSeq, ih]

theorem seq_subset_of {Γ Δ : Bootstrapping.Sequent V L}
    (h : ∀ φ : Bootstrapping.Formula V L, φ ∈ Γ → φ ∈ Δ) : Γ ⊆ Δ := by
  intro x hx
  exact h ⟨x, by simpa using Γ.val_formulaSet x hx⟩ hx

theorem instSeq_subset {Γ Δ : FirstOrder.Sequent (boxL ar)} (h : Δ ⊆ Γ) :
    instSeq σ Δ ⊆ instSeq σ Γ :=
  seq_subset_of fun ψ hψ => by
    rcases (mem_instSeq σ).mp hψ with ⟨φ, hφ, rfl⟩
    exact (mem_instSeq σ).mpr ⟨φ, h hφ, rfl⟩

theorem instSeq_append (Γ Δ : FirstOrder.Sequent (boxL ar)) :
    instSeq σ Γ ∪ instSeq σ Δ ⊆ instSeq σ (Γ ++ Δ) :=
  seq_subset_of fun ψ hψ => by
    rcases Bootstrapping.Sequent.mem_union_iff.mp hψ with h | h
    · rcases (mem_instSeq σ).mp h with ⟨φ, hφ, rfl⟩
      exact (mem_instSeq σ).mpr ⟨φ, List.mem_append_left _ hφ, rfl⟩
    · rcases (mem_instSeq σ).mp h with ⟨φ, hφ, rfl⟩
      exact (mem_instSeq σ).mpr ⟨φ, List.mem_append_right _ hφ, rfl⟩

theorem instSeq_shift (Γ : FirstOrder.Sequent (boxL ar)) :
    instSeq (fun i => (σ i).shift) Γ⁺ = (instSeq σ Γ).shift := by
  induction Γ with
  | nil => simp [instSeq]
  | cons φ Γ ih => simp [instSeq, ih, inst_shift]

/-! ### Derivations -/

/-- The instance of a standard derivation in pure logic, at every choice of the letters. -/
noncomputable def instDer (T : Theory L) [T.Δ₁] : {Γ : FirstOrder.Sequent (boxL ar)} → ⊢ᴸᴷ¹ Γ →
    (σ : (i : Fin m) → Bootstrapping.Semiformula V L (ar i)) →
      T.internalize V ⊢!ᵈᵉʳ instSeq σ Γ
  | _, .identity r v, σ =>
    TDerivation.em (inst σ (FirstOrder.Semiformula.rel r v)) (by simp [instSeq])
      (by simp [instSeq, inst_nrel_eq])
  | _, .cut (φ := φ) (Γ := Γ) (Δ := Δ) dp dn, σ =>
    have b₁ : T.internalize V ⊢!ᵈᵉʳ insert (inst σ φ) (instSeq σ Γ) := instDer T dp σ
    have b₂ : T.internalize V ⊢!ᵈᵉʳ insert (∼(inst σ φ)) (instSeq σ Δ) :=
      (instDer T dn σ).cast (by simp [instSeq, inst_neg])
    (TDerivation.cut' b₁ b₂).wk (instSeq_append σ Γ Δ)
  | _, .contraction d ss, σ => (instDer T d σ).wk (instSeq_subset σ ss)
  | _, .verum, σ => TDerivation.verum (by simp [instSeq])
  | _, .or (φ := φ) (ψ := ψ) (Γ := Γ) d, σ =>
    have b : T.internalize V ⊢!ᵈᵉʳ insert (inst σ φ) (insert (inst σ ψ) (instSeq σ Γ)) :=
      instDer T d σ
    (TDerivation.or b).cast (by simp [instSeq])
  | _, .and (φ := φ) (ψ := ψ) (Γ := Γ) dp dq, σ =>
    have b₁ : T.internalize V ⊢!ᵈᵉʳ insert (inst σ φ) (instSeq σ Γ) := instDer T dp σ
    have b₂ : T.internalize V ⊢!ᵈᵉʳ insert (inst σ ψ) (instSeq σ Γ) := instDer T dq σ
    (TDerivation.and b₁ b₂).cast (by simp [instSeq])
  | _, .all (φ := φ) (Γ := Γ) d, σ =>
    have b : T.internalize V ⊢!ᵈᵉʳ insert (inst σ φ).free (instSeq σ Γ).shift :=
      (instDer T d (fun i => (σ i).shift)).cast (by simp [instSeq, inst_free, instSeq_shift])
    (TDerivation.all b).cast (by simp [instSeq])
  | _, .exs (φ := φ) (Γ := Γ) (t := t) d, σ =>
    have b : T.internalize V ⊢!ᵈᵉʳ insert ((inst σ φ).subst ![tq t]) (instSeq σ Γ) :=
      (instDer T d σ).cast (by simp [instSeq, inst_substs1])
    (TDerivation.exs (tq t) b).cast (by simp [instSeq])

/-- Every instance of a derivable formula of `boxL ar` is provable in every internal theory. -/
theorem inst_provable_of_derivation (T : Theory L) [T.Δ₁] {φ : Proposition (boxL ar)}
    (d : ⊢ᴸᴷ¹ [φ]) : Provable T (inst σ φ).val := by
  have b : T.internalize V ⊢!ᵈᵉʳ insert (inst σ φ) ∅ := instDer T d σ
  exact (TProvable.iff_provable (T := T.internalize V) (σ := inst σ φ)).mp ⟨b⟩

/-- Every instance of a sentence of `boxL ar` that holds in every structure is provable in
every internal theory. -/
theorem inst_provable_of_valid (T : Theory L) [T.Δ₁] (φ : Sentence (boxL ar))
    (h : ∀ (M : Type) [Nonempty M] [Structure (boxL ar) M], M↓[boxL ar] ⊧ φ) :
    Provable T (inst σ (Rewriting.emb φ : Proposition (boxL ar))).val := by
  have h1 : (∅ : Theory (boxL ar)) ⊨[Struc.{0,0} (boxL ar)] φ :=
    consequence_iff.mpr (fun M _ _ _ => h M)
  have h2 : (∅ : Theory (boxL ar)) ⊢ φ := Theory.Proof.complete h1
  have h3 : 𝐋𝐊¹ ⊢ (Rewriting.emb φ : Proposition (boxL ar)) :=
    Theory.Proof.empty_provable_iff_eprovable.mp h2
  obtain ⟨d⟩ := (LK.Proof.provable_def _).mp h3
  exact inst_provable_of_derivation σ T d

#print axioms inst_neg
#print axioms inst_shift
#print axioms inst_substs
#print axioms inst_free
#print axioms instDer
#print axioms inst_provable_of_valid
end generic
end PA194Schematic
