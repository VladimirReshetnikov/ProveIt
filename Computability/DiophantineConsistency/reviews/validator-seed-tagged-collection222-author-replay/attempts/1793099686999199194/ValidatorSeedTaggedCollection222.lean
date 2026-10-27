import ZFCinPA.ValidatorSeedGuardedComprehension222
import ZFCinPA.SetCongruence

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual tagged global-image Collection from the concrete full-seed source.
The binary matrix and all its free parameters may be internally sized.
The support input is unrestricted by the original bound. No CP/GIC premise,
marker interpreter, quotient model or source-axiom-image oracle is supplied. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedTaggedCollection222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open ValidatorSourceFullSeed222 ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222
open ValidatorSeedRawComprehension222 ValidatorSeedGuardedComprehension222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exists_elim {T : InternalTheory V ℒₛₑₜ} {p : Semiformula V ℒₛₑₜ 1}
    {q : Formula V ℒₛₑₜ} (h : T ⊢ p.free 🡒 q.shift) : T ⊢ (∃⁰ p) 🡒 q := by
  have hn : T ⊢ (∼q).shift 🡒 (∼p).free := by
    simpa [Bootstrapping.Semiformula.free] using (show T ⊢ ∼q.shift 🡒 ∼p.free from by cl_prover [h])
  have ha := TProof.generalizeAux hn.get
  have ha' : T ⊢ ∼q 🡒 ∼(∃⁰ p) := by simpa using (show T ⊢ _ from ⟨ha⟩)
  cl_prover [ha']

private theorem exists_project {T : InternalTheory V ℒₛₑₜ} {Γ : List (Formula V ℒₛₑₜ)}
    {p q : Semiformula V ℒₛₑₜ 1} {r : Formula V ℒₛₑₜ}
    (h : Γ ⊢[T] r 🡒 ∃⁰ (p ⋏ q)) : Γ ⊢[T] r 🡒 ∃⁰ p := by
  have he : Γ ⊢[T] (∃⁰ (p ⋏ q)) 🡒 ∃⁰ p := by
    apply TProof.exs_imp_exs!
    simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_and,
      Bootstrapping.Semiformula.substs_and]
    cl_prover
  cl_prover [h,he]

private def source_refl (t : Term V ℒₛₑₜ) : Source V ⊢! eqTerm t t := by
  have hm : (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.refl))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm hm
  change Source V ⊢! ∀⁰ eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 0) at h
  simpa [eqTerm] using TProof.specialize h t

private def pairMatrix (K : Semiformula V ℒₛₑₜ 2) : Semiformula V ℒₛₑₜ 2 :=
  ((∀⁰ ((⌜seedMem 3 0 1⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) 🡒 ∃⁰
      ((K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (∀⁰ ((⌜seedSubset⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 5) 🡒 ∀⁰
          ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 6)⌝,⌜(#1 : SyntacticSemiterm ℒₛₑₜ 6)⌝]) 🡒
            ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 7)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 7)⌝]) ⋏
              (⌜seedMem 7 0 5⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 7)))))))) ⋏
    (∀⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝]) 🡒
      ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#3 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (⌜seedMem 4 0 2⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)))))

private def pairAt (K : Semiformula V ℒₛₑₜ 2) (a c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (pairMatrix K).subst ![c,a]
private def pairExists (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  (pairMatrix K).subst ![Bootstrapping.Semiterm.bvar 0,a.bShift]
private theorem pair_exists (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) :
    Source V ⊢ ∃⁰ pairExists K a := by
  simpa [fullSeedBody,pairExists,pairMatrix,SemitermVec.q] using
    TProof.specialize! (⟨openSeedProof K⟩) a

attribute [local irreducible] pairAt pairExists pairMatrix

private theorem pair_support (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 (memTerm y c 🡒 ∃⁰ K.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0]) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  apply deduct'!
  have hp : [pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [pairAt,pairMatrix,Bootstrapping.Semiformula.substs_and] at hp
  have hs := K!_left hp
  simp only [Bootstrapping.Semiformula.substs_all] at hs
  have hx := TProof.specialize_with_ctx! hs (Bootstrapping.Semiterm.fvar y)
  simp only [Bootstrapping.Semiformula.substs_substs,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_ex,Bootstrapping.Semiformula.substs_and] at hx
  have hx' := exists_project hx
  simpa [pairAt,pairMatrix,memTerm,seedMem,SemitermVec.q,Bootstrapping.Semiformula.substs_substs,
    Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail] using hx'

private theorem pair_request (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 (K.subst ![y,a] 🡒
      ∃⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,a.bShift] ⋏ memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift)) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  apply deduct'!
  have hp : [pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [pairAt,pairMatrix,Bootstrapping.Semiformula.substs_and] at hp
  have hs := K!_right hp
  simp only [Bootstrapping.Semiformula.substs_all] at hs
  have hx := TProof.specialize_with_ctx! hs (Bootstrapping.Semiterm.fvar y)
  simpa [pairAt,pairMatrix,memTerm,seedMem,SemitermVec.q,Bootstrapping.Semiformula.substs_substs,
    Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail] using hx

@[simp] private theorem pairAt_shift (K : Semiformula V ℒₛₑₜ 2) (a c : Term V ℒₛₑₜ) :
    (pairAt K a c).shift=pairAt K.shift a.shift c.shift := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [pairAt,pairMatrix,seedMem,seedSubset,Bootstrapping.Semiformula.shift_substs,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

@[simp] private theorem pairExists_free (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) :
    (pairExists K a).free=pairAt K.shift a.shift (Bootstrapping.Semiterm.fvar 0) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  simp [pairExists,pairAt,pairMatrix,seedMem,seedSubset,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

private theorem source_symm (t u : Term V ℒₛₑₜ) : Source V ⊢ eqTerm t u 🡒 eqTerm u t := by
  have hm : (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.symm))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ (Bootstrapping.Semiformula.nrel Language.Eq.eq
        ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] ⋎
        eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ (eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) 🡒
      eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) := by
    simpa [eqTerm,Bootstrapping.Semiformula.imp_def] using h
  simpa [eqTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₂ h' u t⟩)

private theorem source_mem_congr (t u c : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm t u 🡒 memTerm t c 🡒 memTerm u c := by
  have hm : (⌜(Theory.Eq.relExt Language.Mem.mem : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl (Theory.eqAxiom.relExt _)))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.relExt Language.Mem.mem) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.relExt Language.Mem.mem) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
      ((Bootstrapping.Semiformula.nrel Language.Eq.eq ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 2] ⋎
        (Bootstrapping.Semiformula.nrel Language.Eq.eq ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 3] ⋎ ⊥)) ⋎
        (Bootstrapping.Semiformula.nrel Language.Mem.mem ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] ⋎
        memTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 3))) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ ∀⁰ ∀⁰
      ((eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) ⋏
        (eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 3) ⋏ ⊤)) 🡒
        memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
        memTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 3)) := by
    simpa [eqTerm,memTerm,Bootstrapping.Semiformula.imp_def] using h
  have hh : Source V ⊢ (eqTerm t u ⋏ (eqTerm c c ⋏ ⊤)) 🡒 memTerm t c 🡒 memTerm u c := by
    simpa [eqTerm,memTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₄ h' t c u c⟩)
  have hr : Source V ⊢ eqTerm c c := ⟨source_refl c⟩
  cl_prover [hh,hr]

private theorem source_mem_ext (t u c d : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm t u 🡒 eqTerm c d 🡒 memTerm t c 🡒 memTerm u d := by
  have hm : (⌜(Theory.Eq.relExt Language.Mem.mem : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl (Theory.eqAxiom.relExt _)))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.relExt Language.Mem.mem) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.relExt Language.Mem.mem) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
      ((Bootstrapping.Semiformula.nrel Language.Eq.eq ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 2] ⋎
        (Bootstrapping.Semiformula.nrel Language.Eq.eq ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 3] ⋎ ⊥)) ⋎
        (Bootstrapping.Semiformula.nrel Language.Mem.mem ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] ⋎
        memTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 3))) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ ∀⁰ ∀⁰
      ((eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) ⋏
        (eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 3) ⋏ ⊤)) 🡒
        memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
        memTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 3)) := by
    simpa [eqTerm,memTerm,Bootstrapping.Semiformula.imp_def] using h
  have hh : Source V ⊢ (eqTerm t u ⋏ (eqTerm c d ⋏ ⊤)) 🡒 memTerm t c 🡒 memTerm u d := by
    simpa [eqTerm,memTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₄ h' t c u d⟩)
  cl_prover [hh]

private theorem source_trans (t u v : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm t u 🡒 eqTerm u v 🡒 eqTerm t v := by
  have hm : (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.trans))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ ∀⁰ (Bootstrapping.Semiformula.nrel Language.Eq.eq
        ![Bootstrapping.Semiterm.bvar 2,Bootstrapping.Semiterm.bvar 1] ⋎
        (Bootstrapping.Semiformula.nrel Language.Eq.eq
          ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] ⋎
          eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 0))) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ ∀⁰
      (eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 1) 🡒
       eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) 🡒
       eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 0)) := by
    simpa [eqTerm,Bootstrapping.Semiformula.imp_def] using h
  simpa [eqTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₃ h' v u t⟩)

private def closureTerm {n : ℕ} (K : Semiformula V ℒₛₑₜ 2)
    (c y : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (subsetTerm (Bootstrapping.Semiterm.bvar 0) y.bShift 🡒
    ∀⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] 🡒
      ∃⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 2] ⋏
        memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift.bShift.bShift)))

private def supportBody (K : Semiformula V ℒₛₑₜ 2) (c y : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  K.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0] ⋏ closureTerm K c.bShift y.bShift

private def hitBody (K : Semiformula V ℒₛₑₜ 2) (p c : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  K.subst ![Bootstrapping.Semiterm.bvar 0,p.bShift] ⋏
    memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift

@[simp] private theorem closureTerm_shift {n : ℕ} (K : Semiformula V ℒₛₑₜ 2)
    (c y : Semiterm V ℒₛₑₜ n) :
    (closureTerm K c y).shift=closureTerm K.shift c.shift y.shift := by
  simp [closureTerm,subsetTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] private theorem supportBody_free (K : Semiformula V ℒₛₑₜ 2) (c y : Term V ℒₛₑₜ) :
    (supportBody K c y).free=
      (K.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0] ⋏ closureTerm K.shift c.shift y.shift) := by
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  simp [supportBody,closureTerm,subsetTerm,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

@[simp] private theorem hitBody_free (K : Semiformula V ℒₛₑₜ 2) (p c : Term V ℒₛₑₜ) :
    (hitBody K p c).free=(K.shift.subst ![Bootstrapping.Semiterm.fvar 0,p.shift] ⋏
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) := by
  rcases term_is_fvar p with ⟨p,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [hitBody,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs]


private theorem pair_closure (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 memTerm y c 🡒 closureTerm K c y := by
  unfold pairAt pairMatrix closureTerm
  exact full_member_closure K a c y

private theorem closure_step (K : Semiformula V ℒₛₑₜ 2) (c y p v : Term V ℒₛₑₜ) :
    Source V ⊢ closureTerm K c y 🡒 subsetTerm p y 🡒 K.subst ![v,p] 🡒 ∃⁰ hitBody K p c := by
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  rcases term_is_fvar v with ⟨v,rfl⟩
  apply deduct'!
  apply FiniteContext.deduct!
  have hc : [subsetTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar y),
      closureTerm K (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar y)] ⊢[Source V]
      closureTerm K (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar y) := by_axm!
  unfold closureTerm at hc
  have hs := TProof.specialize_with_ctx! hc (Bootstrapping.Semiterm.fvar p)
  simp [subsetTerm,memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,
    Matrix.vecHead,Matrix.vecTail] at hs
  have hp : [subsetTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar y),
      closureTerm K (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar y)] ⊢[Source V]
      subsetTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar y) := by_axm₀!
  have hp' := hp
  simp [closureTerm,subsetTerm,memTerm] at hp'
  have ha := show _ ⊢[Source V] _ from ⟨hs.get ⨀ hp'.get⟩
  have hv := TProof.specialize_with_ctx! ha (Bootstrapping.Semiterm.fvar v)
  simpa [closureTerm,subsetTerm,hitBody,memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,
    Matrix.vecHead,Matrix.vecTail] using hv

private theorem singleton_spec (p z w : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 (memTerm w p 🡘 eqTerm w z) := by
  apply deduct'!
  have h : [singletonAt p z] ⊢[Source V] singletonAt p z := by_axm₀!
  unfold singletonAt at h
  simpa [singletonAt,eqTerm,memTerm] using TProof.specialize_with_ctx! h w

private theorem singleton_mem (p z : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 memTerm z p := by
  have h := singleton_spec p z z
  have hr : Source V ⊢ eqTerm z z := ⟨source_refl z⟩
  cl_prover [h,hr]

private theorem singleton_unique (p r z a : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm p r 🡒 singletonAt p z 🡒 singletonAt r a 🡒 eqTerm z a := by
  have hz := singleton_mem p z
  have ha := singleton_spec r a z
  have hm := source_mem_ext z z p r
  have hr : Source V ⊢ eqTerm z z := ⟨source_refl z⟩
  have hm' : Source V ⊢ eqTerm p r 🡒 memTerm z p 🡒 memTerm z r := by
    cl_prover [hm,hr]
  have hz' : Source V ⊢ eqTerm p r 🡒 singletonAt p z 🡒 memTerm z r := by
    cl_prover [hm',hz]
  cl_prover [hz',ha]

@[simp] private theorem singletonAt_shift (p z : Term V ℒₛₑₜ) :
    (singletonAt p z).shift=singletonAt p.shift z.shift := by
  simp [singletonAt,eqTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] private theorem subsetTerm_shift {n : ℕ} (p y : Semiterm V ℒₛₑₜ n) :
    (subsetTerm p y).shift=subsetTerm p.shift y.shift := by
  simp [subsetTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] private theorem singletonBody_free' (t : Term V ℒₛₑₜ) :
    (singletonBody t).free=singletonAt (Bootstrapping.Semiterm.fvar 0) t.shift := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  simp [singletonBody,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    SemitermVec.q]

attribute [local irreducible] singletonAt subsetTerm closureTerm supportBody hitBody

private theorem singleton_subset (p z a : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 memTerm z a 🡒 subsetTerm p a := by
  apply deduct'!
  apply FiniteContext.deduct!
  unfold subsetTerm
  apply TProof.generalize!
  have hs := FiniteContext.of'! (Γ := [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift)
    (singleton_spec p.shift z.shift (Bootstrapping.Semiterm.fvar 0))
  have hm := FiniteContext.of'! (Γ := [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift)
    (source_mem_congr z.shift (Bootstrapping.Semiterm.fvar 0) a.shift)
  have he := FiniteContext.of'! (Γ := [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift)
    (source_symm (Bootstrapping.Semiterm.fvar 0) z.shift)
  have hp : [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift ⊢[Source V]
      singletonAt p.shift z.shift := by simp only [List.map_cons,List.map_nil,singletonAt_shift]; exact by_axm!
  have hz : [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift ⊢[Source V]
      memTerm z.shift a.shift := by simp [memTerm] ; exact by_axm₀!
  simpa [memTerm,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using
    (show [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift ⊢[Source V]
      memTerm (Bootstrapping.Semiterm.fvar 0) p.shift 🡒 memTerm (Bootstrapping.Semiterm.fvar 0) a.shift from by
        cl_prover [hs,hm,he,hp,hz])

private theorem source_mem_right (z a b : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm a b 🡒 memTerm z a 🡒 memTerm z b := by
  have h := source_mem_ext z z a b
  have hr : Source V ⊢ eqTerm z z := ⟨source_refl z⟩
  cl_prover [h,hr]

private theorem source_irrefl (t : Term V ℒₛₑₜ) : Source V ⊢ ∼memTerm t t := by
  have hm : (⌜irreflexiveSentence⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inr (by simp)))
  have h : Source V ⊢! (⌜(Rewriting.emb irreflexiveSentence : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm hm
  have hv : (fun i : Fin 2 => (⌜(![#0,#0] i : SyntacticSemiterm ℒₛₑₜ 1)⌝ :
      Semiterm V ℒₛₑₜ 1)) = ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  have h' : Source V ⊢! ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0)
    (Bootstrapping.Semiterm.bvar 0) 🡒 ⊥) := by
    simpa [irreflexiveSentence,FirstOrder.Semiformula.Operator.mem_def,
      memTerm,FirstOrder.Semiformula.quote_def,hv] using h
  have ht : Source V ⊢ memTerm t t 🡒 ⊥ := by
    simpa [memTerm] using (show Source V ⊢ _ from ⟨TProof.specialize h' t⟩)
  cl_prover [ht]

@[simp] private theorem emptyAt_shift (t : Term V ℒₛₑₜ) :
    (emptyAt t).shift=emptyAt t.shift := by
  simp [emptyAt,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

private theorem empty_spec (t z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼memTerm z t := by
  apply deduct'!
  have h : [emptyAt t] ⊢[Source V] emptyAt t := by_axm₀!
  unfold emptyAt at h
  have hz : [emptyAt t] ⊢[Source V] memTerm z t 🡒 ⊥ := by
    simpa [emptyAt,memTerm] using TProof.specialize_with_ctx! h z
  cl_prover [hz]

private theorem empty_subset (t a : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 subsetTerm t a := by
  apply deduct'!
  unfold subsetTerm
  apply TProof.generalize!
  have he := FiniteContext.of'! (Γ := [emptyAt t].map Bootstrapping.Semiformula.shift)
    (empty_spec t.shift (Bootstrapping.Semiterm.fvar 0))
  have hh : [emptyAt t].map Bootstrapping.Semiformula.shift ⊢[Source V] emptyAt t.shift := by
    simp only [List.map_cons,List.map_nil,emptyAt_shift]
    exact by_axm₀!
  simpa [memTerm,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using
    (show [emptyAt t].map Bootstrapping.Semiformula.shift ⊢[Source V]
      memTerm (Bootstrapping.Semiterm.fvar 0) t.shift 🡒
        memTerm (Bootstrapping.Semiterm.fvar 0) a.shift from by cl_prover [he,hh])

private theorem singleton_ne_empty (t r z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 singletonAt r z 🡒 ∼eqTerm r t := by
  have hm := singleton_mem r z
  have hx := source_mem_right z r t
  have he := empty_spec t z
  cl_prover [hm,hx,he]

private def supportCore (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 := K.subst ![z.bShift,Bootstrapping.Semiterm.bvar 0]
@[simp] private theorem supportCore_free (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    (supportCore K z).free=K.shift.subst ![z.shift,Bootstrapping.Semiterm.fvar 0] := by
  rcases term_is_fvar z with ⟨z,rfl⟩
  simp [supportCore,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]

private theorem hit_member (K : Semiformula V ℒₛₑₜ 2) (p c z : Term V ℒₛₑₜ)
    (H : Formula V ℒₛₑₜ)
    (h : Source V ⊢ H.shift 🡒
      K.shift.subst ![Bootstrapping.Semiterm.fvar 0,p.shift] 🡒
        eqTerm (Bootstrapping.Semiterm.fvar 0) z.shift) :
    Source V ⊢ H 🡒 (∃⁰ hitBody K p c) 🡒 memTerm z c := by
  have he : Source V ⊢ (∃⁰ hitBody K p c) 🡒 (H 🡒 memTerm z c) := by
    apply exists_elim
    rw [hitBody_free]
    have hm := source_mem_congr (Bootstrapping.Semiterm.fvar 0) z.shift c.shift
    simpa only [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_rel,
      memTerm,Matrix.map_cons,Matrix.map_nil] using
      (show Source V ⊢
        (K.shift.subst ![Bootstrapping.Semiterm.fvar 0,p.shift] ⋏
          memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒
        (H.shift 🡒 memTerm z.shift c.shift) from by cl_prover [h,hm])
  cl_prover [he]

private theorem rawPairAt_spec (x y c z : Term V ℒₛₑₜ) :
    Source V ⊢ rawPairAt x y c 🡒 (memTerm z c 🡘 (eqTerm z x ⋎ eqTerm z y)) := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  apply deduct'!
  have h : [rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [rawPairAt,rawPairBody,Bootstrapping.Semiformula.substs_all] at h
  simpa [rawPairAt,rawPairBody,eqTerm,memTerm,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z

attribute [local irreducible] rawPairMatrix rawPairBody rawPairAt supportCore

private def rootCondition (B t r : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  emptyAt t ⋏ (∼eqTerm B t ⋏ rawPairAt B t r)

@[simp] private theorem rootCondition_shift (B t r : Term V ℒₛₑₜ) :
    (rootCondition B t r).shift=rootCondition B.shift t.shift r.shift := by
  simp [rootCondition,eqTerm]
private theorem root_ne_empty (B t r : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 ∼eqTerm r t := by
  have hs := rawPairAt_spec B t r B
  have hb : Source V ⊢ eqTerm B B := ⟨source_refl B⟩
  have hm := source_mem_right B r t
  have he := empty_spec t B
  unfold rootCondition
  cl_prover [hs,hb,hm,he]

private theorem root_not_singleton (B t r p z : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 singletonAt p z 🡒 ∼eqTerm p r := by
  have hB := rawPairAt_spec B t r B
  have ht := rawPairAt_spec B t r t
  have hBB : Source V ⊢ eqTerm B B := ⟨source_refl B⟩
  have htt : Source V ⊢ eqTerm t t := ⟨source_refl t⟩
  have hs := source_symm p r
  have hmB := source_mem_right B r p
  have hmt := source_mem_right t r p
  have hzB := singleton_spec p z B
  have hzt := singleton_spec p z t
  have hsz := source_symm t z
  have htr := source_trans B z t
  have hpB : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 memTerm B p := by
    cl_prover [hB,hBB,hs,hmB]
  have hpt : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 memTerm t p := by
    cl_prover [ht,htt,hs,hmt]
  have hBz : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 singletonAt p z 🡒 eqTerm B z := by
    cl_prover [hpB,hzB]
  have htz : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 singletonAt p z 🡒 eqTerm t z := by
    cl_prover [hpt,hzt]
  unfold rootCondition
  cl_prover 48 [hBz,htz,hsz,htr]

private theorem empty_not_singleton (t z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼singletonAt t z := by
  cl_prover [empty_spec t z,singleton_mem t z]

private theorem aug_spec (θ : Semiformula V ℒₛₑₜ 1) (U E z : Term V ℒₛₑₜ) :
    Source V ⊢ rawAugAt θ U E 🡒 (memTerm z E 🡘 (eqTerm z U ⋎ (memTerm z U ⋏ θ.subst ![z]))) := by
  rcases term_is_fvar U with ⟨U,rfl⟩
  rcases term_is_fvar E with ⟨E,rfl⟩
  apply deduct'!
  have h : [rawAugAt θ (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar E)] ⊢[Source V] rawAugAt θ (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar E) := by_axm₀!
  simp only [rawAugAt,rawAugBody,Bootstrapping.Semiformula.substs_all] at h
  simpa [rawAugAt,rawAugBody,memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z


private instance source_contains_eq : 𝗘𝗤 ℒₛₑₜ ⪯ seedTheory :=
  Axiomatized.le_of_subset (fun _ h => Or.inl (Or.inl h))

/-- Actual source equality replacement in the second slot of an arbitrary
internal binary matrix; no congruence premise about the matrix is supplied. -/
theorem matrix_second_transport (θ : Semiformula V ℒₛₑₜ 2)
    (y x' x : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm x' x 🡒 θ.subst ![y,x'] 🡒 θ.subst ![y,x] := by
  have h := SetCongruence.setReplace seedTheory
    (θ.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0]) x' x
  rcases term_is_fvar y with ⟨y,rfl⟩
  simpa [eqTerm,SetCongruence.eqAtom,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail] using h

private theorem all_under (H : Formula V ℒₛₑₜ) (p : Semiformula V ℒₛₑₜ 1)
    (h : Source V ⊢ H.shift 🡒 p.free) : Source V ⊢ H 🡒 ∀⁰ p := by
  apply deduct'!
  apply TProof.generalize!
  have hh : [H].map Bootstrapping.Semiformula.shift ⊢[Source V] H.shift := by
    simp only [List.map_cons,List.map_nil]; exact by_axm₀!
  exact ⟨(FiniteContext.of'! (Γ := [H].map Bootstrapping.Semiformula.shift) h).get ⨀ hh.get⟩

private def imageCore (θ : Semiformula V ℒₛₑₜ 2) (t p y : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    (singTerm p.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
      (memTerm t.bShift y.bShift ⋏ θ.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0]))
private def supportImage (θ : Semiformula V ℒₛₑₜ 2) (t y : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    θ.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0]
private def selectedImage (θ : Semiformula V ℒₛₑₜ 2) (t c x : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift ⋏
      θ.subst ![Bootstrapping.Semiterm.bvar 0,x.bShift])
private def givenImage (θ : Semiformula V ℒₛₑₜ 2) (t x : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    θ.subst ![Bootstrapping.Semiterm.bvar 0,x.bShift]

def collectionMatrix (θ : Semiformula V ℒₛₑₜ 2) (E t r : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 2 :=
  (eqTerm (Bootstrapping.Semiterm.bvar 1) r.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) E.bShift.bShift) ⋎
  ((eqTerm (Bootstrapping.Semiterm.bvar 1) t.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift.bShift) ⋎
    ∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
      (singTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 0) ⋏
        (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 1) ⋏
          θ.subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0]))))

@[simp] theorem collectionMatrix_shift (θ : Semiformula V ℒₛₑₜ 2) (E t r : Term V ℒₛₑₜ) :
    (collectionMatrix θ E t r).shift=collectionMatrix θ.shift E.shift t.shift r.shift := by
  simp [collectionMatrix,eqTerm,memTerm,singTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem imageCore_free (θ : Semiformula V ℒₛₑₜ 2) (t p y : Term V ℒₛₑₜ) :
    (imageCore θ t p y).free=
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        (singletonAt p.shift (Bootstrapping.Semiterm.fvar 0) ⋏
          (memTerm t.shift y.shift ⋏ θ.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0]))) := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  simp [imageCore,singTerm,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem supportImage_shift (θ : Semiformula V ℒₛₑₜ 2) (t y : Term V ℒₛₑₜ) :
    (supportImage θ t y).shift=supportImage θ.shift t.shift y.shift := by
  simp [supportImage,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem selectedImage_shift (θ : Semiformula V ℒₛₑₜ 2) (t c x : Term V ℒₛₑₜ) :
    (selectedImage θ t c x).shift=selectedImage θ.shift t.shift c.shift x.shift := by
  simp [selectedImage,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem givenImage_shift (θ : Semiformula V ℒₛₑₜ 2) (t x : Term V ℒₛₑₜ) :
    (givenImage θ t x).shift=givenImage θ.shift t.shift x.shift := by
  simp [givenImage,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem collectionMatrix_subst (θ : Semiformula V ℒₛₑₜ 2) (E t r y p : Term V ℒₛₑₜ) :
    (collectionMatrix θ E t r).subst ![y,p]=
      ((eqTerm p r ⋏ eqTerm y E) ⋎ ((eqTerm p t ⋏ eqTerm y t) ⋎ ∃⁰ imageCore θ t p y)) := by
  rcases term_is_fvar E with ⟨E,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  simp [collectionMatrix,imageCore,singTerm,eqTerm,memTerm,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

attribute [local irreducible] collectionMatrix imageCore supportImage selectedImage givenImage rootCondition

private theorem image_core_singleton (θ : Semiformula V ℒₛₑₜ 2) (t p y x : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ imageCore θ t p y) 🡒 singletonAt p x 🡒
      (memTerm t y ⋏ θ.subst ![y,x]) := by
  apply exists_elim
  rw [imageCore_free]
  have hu := singleton_unique p.shift p.shift (Bootstrapping.Semiterm.fvar 0) x.shift
  have hr : Source V ⊢ eqTerm p.shift p.shift := ⟨source_refl _⟩
  have ht := matrix_second_transport θ.shift y.shift (Bootstrapping.Semiterm.fvar 0) x.shift
  have hu' : Source V ⊢ singletonAt p.shift (Bootstrapping.Semiterm.fvar 0) 🡒
      singletonAt p.shift x.shift 🡒 eqTerm (Bootstrapping.Semiterm.fvar 0) x.shift := by
    cl_prover [hu,hr]
  simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    singletonAt_shift,memTerm,Bootstrapping.Semiformula.shift_substs,
    Matrix.vecHead,Matrix.vecTail] using
    (show Source V ⊢
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        (singletonAt p.shift (Bootstrapping.Semiterm.fvar 0) ⋏
          (memTerm t.shift y.shift ⋏ θ.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0]))) 🡒
      singletonAt p.shift x.shift 🡒 (memTerm t.shift y.shift ⋏ θ.shift.subst ![y.shift,x.shift]) from by
        cl_prover [hu',ht])

private theorem image_core_not_singleton (θ : Semiformula V ℒₛₑₜ 2) (E t r y : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ imageCore θ t r y) 🡒 rootCondition E t r 🡒 ⊥ := by
  apply exists_elim
  rw [imageCore_free]
  have hs := root_not_singleton E.shift t.shift r.shift r.shift (Bootstrapping.Semiterm.fvar 0)
  have hr : Source V ⊢ eqTerm r.shift r.shift := ⟨source_refl _⟩
  simpa only [Bootstrapping.Semiformula.shift_imp,rootCondition_shift,
    Bootstrapping.Semiformula.shift_falsum] using
    (show Source V ⊢
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        (singletonAt r.shift (Bootstrapping.Semiterm.fvar 0) ⋏
          (memTerm t.shift y.shift ⋏ θ.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0]))) 🡒
        rootCondition E.shift t.shift r.shift 🡒 ⊥ from by cl_prover [hs,hr])

private theorem image_core_not_empty (θ : Semiformula V ℒₛₑₜ 2) (t y : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ imageCore θ t t y) 🡒 emptyAt t 🡒 ⊥ := by
  apply exists_elim
  rw [imageCore_free]
  have he := empty_not_singleton t.shift (Bootstrapping.Semiterm.fvar 0)
  simpa only [Bootstrapping.Semiformula.shift_imp,emptyAt_shift,
    Bootstrapping.Semiformula.shift_falsum] using
    (show Source V ⊢
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        (singletonAt t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
          (memTerm t.shift y.shift ⋏ θ.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0]))) 🡒
        emptyAt t.shift 🡒 ⊥ from by cl_prover [he])

private theorem collection_root_value (θ : Semiformula V ℒₛₑₜ 2) (E t r y : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition E t r 🡒 (collectionMatrix θ E t r).subst ![y,r] 🡒 eqTerm y E := by
  rw [collectionMatrix_subst]
  cl_prover [root_ne_empty E t r,image_core_not_singleton θ E t r y]

private theorem collection_empty_value (θ : Semiformula V ℒₛₑₜ 2) (E t r y : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition E t r 🡒 (collectionMatrix θ E t r).subst ![y,t] 🡒 eqTerm y t := by
  rw [collectionMatrix_subst]
  have he := image_core_not_empty θ t y
  have he' : Source V ⊢ (∃⁰ imageCore θ t t y) 🡒 rootCondition E t r 🡒 ⊥ := by
    unfold rootCondition; cl_prover [he]
  cl_prover [root_ne_empty E t r,source_symm t r,he']

private theorem collection_singleton_value (θ : Semiformula V ℒₛₑₜ 2) (E t r p x y : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition E t r 🡒 singletonAt p x 🡒
      (collectionMatrix θ E t r).subst ![y,p] 🡒 (memTerm t y ⋏ θ.subst ![y,x]) := by
  rw [collectionMatrix_subst]
  have he := singleton_ne_empty t p x
  have he' : Source V ⊢ rootCondition E t r 🡒 singletonAt p x 🡒 ∼eqTerm p t := by
    unfold rootCondition; cl_prover [he]
  cl_prover [root_not_singleton E t r p x,he',image_core_singleton θ t p y x]

private theorem collection_first (θ : Semiformula V ℒₛₑₜ 2) (E t r c : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition E t r 🡒 pairAt (collectionMatrix θ E t r) r c 🡒 memTerm E c := by
  have hh := hit_member (collectionMatrix θ E t r) r c E (rootCondition E t r) (by
    simpa only [rootCondition_shift,collectionMatrix_shift] using
      collection_root_value θ.shift E.shift t.shift r.shift (Bootstrapping.Semiterm.fvar 0))
  have hr : Source V ⊢ pairAt (collectionMatrix θ E t r) r c 🡒
      (collectionMatrix θ E t r).subst ![E,r] 🡒 ∃⁰ hitBody (collectionMatrix θ E t r) r c :=
    by simpa only [hitBody] using pair_request (collectionMatrix θ E t r) r c E
  have hk : Source V ⊢ (collectionMatrix θ E t r).subst ![E,r] := by
    rw [collectionMatrix_subst]
    have hE : Source V ⊢ eqTerm E E := ⟨source_refl E⟩
    have hR : Source V ⊢ eqTerm r r := ⟨source_refl r⟩
    cl_prover [hE,hR]
  cl_prover [hh,hr,hk]

private theorem collection_tag (θ : Semiformula V ℒₛₑₜ 2) (E t r c : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition E t r 🡒 pairAt (collectionMatrix θ E t r) r c 🡒 memTerm t c := by
  have hh := hit_member (collectionMatrix θ E t r) t c t (rootCondition E t r) (by
    simpa only [rootCondition_shift,collectionMatrix_shift] using
      collection_empty_value θ.shift E.shift t.shift r.shift (Bootstrapping.Semiterm.fvar 0))
  have hc := pair_closure (collectionMatrix θ E t r) r c E
  have hf := collection_first θ E t r c
  have hstep := closure_step (collectionMatrix θ E t r) c E t t
  have he : Source V ⊢ rootCondition E t r 🡒 subsetTerm t E := by
    have h := empty_subset t E
    unfold rootCondition; cl_prover [h]
  have hk : Source V ⊢ (collectionMatrix θ E t r).subst ![t,t] := by
    rw [collectionMatrix_subst]
    have ht : Source V ⊢ eqTerm t t := ⟨source_refl t⟩
    cl_prover [ht]
  have hcl : Source V ⊢ rootCondition E t r 🡒 pairAt (collectionMatrix θ E t r) r c 🡒
      closureTerm (collectionMatrix θ E t r) c E := by cl_prover [hc,hf]
  have hhit : Source V ⊢ rootCondition E t r 🡒 pairAt (collectionMatrix θ E t r) r c 🡒
      ∃⁰ hitBody (collectionMatrix θ E t r) t c := by cl_prover 80 [hcl,he,hstep,hk]
  cl_prover [hhit,hh]

private theorem exists_intro (p : Semiformula V ℒₛₑₜ 1) (x : Term V ℒₛₑₜ) :
    Source V ⊢ p.subst ![x] 🡒 ∃⁰ p := by
  have hn : Source V ⊢ ∼(∃⁰ p) 🡒 ∼(p.subst ![x]) := by
    apply deduct'!
    have h : [∼(∃⁰ p)] ⊢[Source V] ∀⁰ ∼p := by
      simpa using (by_axm₀! (𝓢 := Source V) (Γ := []) (φ := ∼(∃⁰ p)))
    simpa using TProof.specialize_with_ctx! h x
  cl_prover [hn]

private theorem image_core_intro (θ : Semiformula V ℒₛₑₜ 2) (t p y x : Term V ℒₛₑₜ) :
    Source V ⊢ memTerm t x 🡒 singletonAt p x 🡒 memTerm t y 🡒 θ.subst ![y,x] 🡒
      ∃⁰ imageCore θ t p y := by
  have h := exists_intro (imageCore θ t p y) x
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar x with ⟨x,rfl⟩
  simp only [imageCore,Bootstrapping.Semiformula.substs_and] at h
  have h' : Source V ⊢
      (memTerm (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar x) ⋏
        (singletonAt (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar x) ⋏
          (memTerm (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar y) ⋏
            θ.subst ![Bootstrapping.Semiterm.fvar y,Bootstrapping.Semiterm.fvar x]))) 🡒
      ∃⁰ imageCore θ (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar p)
        (Bootstrapping.Semiterm.fvar y) := by
    simpa [imageCore,singTerm,singletonAt,memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,
      SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using h
  cl_prover [h']

private theorem image_projection (θ : Semiformula V ℒₛₑₜ 2) (t p y : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ imageCore θ t p y) 🡒 ∃⁰ supportImage θ t y := by
  apply TProof.exs_imp_exs!
  rw [imageCore_free]
  simp [supportImage,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail]
  cl_prover

private def outputProperty (θ : Semiformula V ℒₛₑₜ 2) (E t y : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  eqTerm y E ⋎ (eqTerm y t ⋎ ∃⁰ supportImage θ t y)
@[simp] private theorem outputProperty_shift (θ : Semiformula V ℒₛₑₜ 2) (E t y : Term V ℒₛₑₜ) :
    (outputProperty θ E t y).shift=outputProperty θ.shift E.shift t.shift y.shift := by
  simp [outputProperty,eqTerm]
attribute [local irreducible] outputProperty

private theorem collection_cover (θ : Semiformula V ℒₛₑₜ 2) (E t r c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (collectionMatrix θ E t r) r c 🡒 memTerm y c 🡒 outputProperty θ E t y := by
  have he : Source V ⊢ (∃⁰ supportCore (collectionMatrix θ E t r) y) 🡒 outputProperty θ E t y := by
    apply exists_elim
    rw [supportCore_free,collectionMatrix_shift,collectionMatrix_subst,outputProperty_shift]
    have hp := image_projection θ.shift t.shift (Bootstrapping.Semiterm.fvar 0) y.shift
    unfold outputProperty
    cl_prover [hp]
  have hs : Source V ⊢ pairAt (collectionMatrix θ E t r) r c 🡒 memTerm y c 🡒
      ∃⁰ supportCore (collectionMatrix θ E t r) y := by
    simpa only [supportCore] using pair_support (collectionMatrix θ E t r) r c y
  cl_prover [he,hs]

private theorem collection_support (θ : Semiformula V ℒₛₑₜ 2) (E t r c y : Term V ℒₛₑₜ) :
    Source V ⊢ ∼memTerm t E 🡒 pairAt (collectionMatrix θ E t r) r c 🡒
      memTerm t y 🡒 memTerm y c 🡒 ∃⁰ supportImage θ t y := by
  have hs := collection_cover θ E t r c y
  have he := source_mem_right t y E
  have ht := source_mem_right t y t
  have hi := source_irrefl t
  unfold outputProperty at hs
  cl_prover 80 [hs,he,ht,hi]

private theorem hit_selected (θ : Semiformula V ℒₛₑₜ 2) (E t r p c x : Term V ℒₛₑₜ) :
    Source V ⊢ (rootCondition E t r ⋏ singletonAt p x) 🡒
      (∃⁰ hitBody (collectionMatrix θ E t r) p c) 🡒 ∃⁰ selectedImage θ t c x := by
  apply deduct'!
  apply TProof.exs_imp_exs!
  rw [hitBody_free,collectionMatrix_shift]
  let Γ := [rootCondition E t r ⋏ singletonAt p x].map Bootstrapping.Semiformula.shift
  have hH : Γ ⊢[Source V] rootCondition E.shift t.shift r.shift ⋏ singletonAt p.shift x.shift := by
    simp only [Γ,List.map_cons,List.map_nil,Bootstrapping.Semiformula.shift_and,
      rootCondition_shift,singletonAt_shift]; exact by_axm₀!
  have hv := FiniteContext.of'! (Γ := Γ)
    (collection_singleton_value θ.shift E.shift t.shift r.shift p.shift x.shift
      (Bootstrapping.Semiterm.fvar 0))
  have h : Γ ⊢[Source V]
      ((collectionMatrix θ.shift E.shift t.shift r.shift).subst ![Bootstrapping.Semiterm.fvar 0,p.shift] ⋏
        memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        (memTerm (Bootstrapping.Semiterm.fvar 0) c.shift ⋏
          θ.shift.subst ![Bootstrapping.Semiterm.fvar 0,x.shift])) := by cl_prover [hv,hH]
  simpa [Γ,selectedImage,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail] using h

private theorem collection_selected (θ : Semiformula V ℒₛₑₜ 2) (E t r c x y : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition E t r 🡒 pairAt (collectionMatrix θ E t r) r c 🡒
      memTerm t x 🡒 memTerm x E 🡒 memTerm t y 🡒 θ.subst ![y,x] 🡒
        ∃⁰ selectedImage θ t c x := by
  have he : Source V ⊢ (∃⁰ singletonBody x) 🡒
      (rootCondition E t r 🡒 pairAt (collectionMatrix θ E t r) r c 🡒
        memTerm t x 🡒 memTerm x E 🡒 memTerm t y 🡒 θ.subst ![y,x] 🡒 ∃⁰ selectedImage θ t c x) := by
    apply exists_elim
    rw [singletonBody_free']
    let p : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
    have hh := hit_selected θ.shift E.shift t.shift r.shift p c.shift x.shift
    have hf := collection_first θ.shift E.shift t.shift r.shift c.shift
    have hc := pair_closure (collectionMatrix θ.shift E.shift t.shift r.shift) r.shift c.shift E.shift
    have hs := singleton_subset p x.shift E.shift
    have hstep := closure_step (collectionMatrix θ.shift E.shift t.shift r.shift) c.shift E.shift p y.shift
    have hi := image_core_intro θ.shift t.shift p y.shift x.shift
    have hk : Source V ⊢ memTerm t.shift x.shift 🡒 singletonAt p x.shift 🡒
        memTerm t.shift y.shift 🡒 θ.shift.subst ![y.shift,x.shift] 🡒
        (collectionMatrix θ.shift E.shift t.shift r.shift).subst ![y.shift,p] := by
      rw [collectionMatrix_subst]; cl_prover [hi]
    have hcl : Source V ⊢ rootCondition E.shift t.shift r.shift 🡒
        pairAt (collectionMatrix θ.shift E.shift t.shift r.shift) r.shift c.shift 🡒
        closureTerm (collectionMatrix θ.shift E.shift t.shift r.shift) c.shift E.shift := by
      cl_prover [hf,hc]
    have hhit : Source V ⊢ singletonAt p x.shift 🡒 memTerm x.shift E.shift 🡒
        memTerm t.shift x.shift 🡒 memTerm t.shift y.shift 🡒 θ.shift.subst ![y.shift,x.shift] 🡒
        closureTerm (collectionMatrix θ.shift E.shift t.shift r.shift) c.shift E.shift 🡒
        ∃⁰ hitBody (collectionMatrix θ.shift E.shift t.shift r.shift) p c.shift := by
      cl_prover 80 [hs,hk,hstep]
    have h : Source V ⊢ singletonAt p x.shift 🡒 rootCondition E.shift t.shift r.shift 🡒
        pairAt (collectionMatrix θ.shift E.shift t.shift r.shift) r.shift c.shift 🡒
        memTerm t.shift x.shift 🡒 memTerm x.shift E.shift 🡒 memTerm t.shift y.shift 🡒
        θ.shift.subst ![y.shift,x.shift] 🡒 ∃⁰ selectedImage θ.shift t.shift c.shift x.shift := by
      cl_prover 96 [hcl,hhit,hh]
    simpa [p,Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      rootCondition_shift,pairAt_shift,collectionMatrix_shift,selectedImage_shift,memTerm,
      Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail] using h
  exact ⟨he.get ⨀ (singleton_object x).get⟩

private def envelopeCondition (a t E : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  emptyAt t ⋏ (memTerm t a ⋏ rawAugAt (tagMatrix t) a E)
@[simp] private theorem rawAugAt_shift' (θ : Semiformula V ℒₛₑₜ 1) (a c : Term V ℒₛₑₜ) :
    (rawAugAt θ a c).shift=rawAugAt θ.shift a.shift c.shift := by
  simp [rawAugAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem envelopeCondition_shift (a t E : Term V ℒₛₑₜ) :
    (envelopeCondition a t E).shift=envelopeCondition a.shift t.shift E.shift := by
  simp [envelopeCondition,memTerm]
private theorem tagged_ne (a t : Term V ℒₛₑₜ) :
    Source V ⊢ memTerm t a 🡒 ∼eqTerm a t := by
  cl_prover [source_mem_right t a t,source_irrefl t]
private theorem envelope_ne (a t E : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition a t E 🡒 ∼eqTerm E t := by
  have hs := aug_spec (tagMatrix t) a E a
  have hr : Source V ⊢ eqTerm a a := ⟨source_refl a⟩
  have hm := source_mem_right a E t
  have he := empty_spec t a
  unfold envelopeCondition
  cl_prover [hs,hr,hm,he]
private theorem envelope_untagged (a t E : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition a t E 🡒 ∼memTerm t E := by
  have hs := aug_spec (tagMatrix t) a E t
  have he := source_symm t a
  have hi := source_irrefl t
  have ha := tagged_ne a t
  have hs' : Source V ⊢ rawAugAt (tagMatrix t) a E 🡒
      (memTerm t E 🡘 (eqTerm t a ⋎ (memTerm t a ⋏ memTerm t t))) := by
    simpa [tagMatrix,memTerm] using hs
  unfold envelopeCondition
  cl_prover 80 [hs',he,hi,ha]
private theorem envelope_member (a t E x : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition a t E 🡒 memTerm t x 🡒 memTerm x a 🡒 memTerm x E := by
  have hs := aug_spec (tagMatrix t) a E x
  have hs' : Source V ⊢ rawAugAt (tagMatrix t) a E 🡒
      (memTerm x E 🡘 (eqTerm x a ⋎ (memTerm x a ⋏ memTerm t x))) := by
    simpa [tagMatrix,memTerm] using hs
  unfold envelopeCondition
  cl_prover [hs']

private def collectionCondition (θ : Semiformula V ℒₛₑₜ 2) (a t E r c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  envelopeCondition a t E ⋏ (rootCondition E t r ⋏ pairAt (collectionMatrix θ E t r) r c)
@[simp] private theorem collectionCondition_shift (θ : Semiformula V ℒₛₑₜ 2) (a t E r c : Term V ℒₛₑₜ) :
    (collectionCondition θ a t E r c).shift=
      collectionCondition θ.shift a.shift t.shift E.shift r.shift c.shift := by
  simp [collectionCondition]

attribute [local irreducible] envelopeCondition collectionCondition

private theorem support_under (θ : Semiformula V ℒₛₑₜ 2) (a t E r c y : Term V ℒₛₑₜ) :
    Source V ⊢ collectionCondition θ a t E r c 🡒 memTerm t y 🡒 memTerm y c 🡒
      ∃⁰ supportImage θ t y := by
  have hs := collection_support θ E t r c y
  have hu := envelope_untagged a t E
  unfold collectionCondition
  cl_prover [hs,hu]

private theorem selected_under_point (θ : Semiformula V ℒₛₑₜ 2) (a t E r c x y : Term V ℒₛₑₜ) :
    Source V ⊢ collectionCondition θ a t E r c 🡒 memTerm t x 🡒 memTerm x a 🡒
      memTerm t y 🡒 θ.subst ![y,x] 🡒 ∃⁰ selectedImage θ t c x := by
  have hs := collection_selected θ E t r c x y
  have hm := envelope_member a t E x
  unfold collectionCondition
  cl_prover 80 [hs,hm]

@[simp] private theorem givenImage_free (θ : Semiformula V ℒₛₑₜ 2) (t x : Term V ℒₛₑₜ) :
    (givenImage θ t x).free=
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        θ.shift.subst ![Bootstrapping.Semiterm.fvar 0,x.shift]) := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar x with ⟨x,rfl⟩
  simp [givenImage,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail]

private theorem selected_under (θ : Semiformula V ℒₛₑₜ 2) (a t E r c x : Term V ℒₛₑₜ) :
    Source V ⊢ collectionCondition θ a t E r c 🡒 memTerm t x 🡒 memTerm x a 🡒
      (∃⁰ givenImage θ t x) 🡒 ∃⁰ selectedImage θ t c x := by
  have he : Source V ⊢ (∃⁰ givenImage θ t x) 🡒
      (collectionCondition θ a t E r c 🡒 memTerm t x 🡒 memTerm x a 🡒
        ∃⁰ selectedImage θ t c x) := by
    apply exists_elim
    rw [givenImage_free]
    have hp := selected_under_point θ.shift a.shift t.shift E.shift r.shift c.shift x.shift
      (Bootstrapping.Semiterm.fvar 0)
    simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      collectionCondition_shift,selectedImage_shift,memTerm] using
      (show Source V ⊢
        (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
          θ.shift.subst ![Bootstrapping.Semiterm.fvar 0,x.shift]) 🡒
        collectionCondition θ.shift a.shift t.shift E.shift r.shift c.shift 🡒
          memTerm t.shift x.shift 🡒 memTerm x.shift a.shift 🡒
          ∃⁰ selectedImage θ.shift t.shift c.shift x.shift from by cl_prover [hp])
  cl_prover [he]

/-- Global support does not restrict its input to the original bound. -/
def collectionBody (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    ((∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
      memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
        ∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
          θ.subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0]))) ⋏
    (∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
      memTerm (Bootstrapping.Semiterm.bvar 0) a.bShift.bShift 🡒
      (∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
        θ.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1])) 🡒
      ∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
        (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) ⋏
          θ.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1])))))
def collectionAt (θ : Semiformula V ℒₛₑₜ 2) (a t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (collectionBody θ a t).subst ![c]
def collectionConclusion (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  emptyAt t 🡒 memTerm t a 🡒 ∃⁰ collectionBody θ a t

private def supportAll (θ : Semiformula V ℒₛₑₜ 2) (t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
    memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡒
      ∃⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
        θ.subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0]))
private def coverageAll (θ : Semiformula V ℒₛₑₜ 2) (a t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
    memTerm (Bootstrapping.Semiterm.bvar 0) a.bShift 🡒
    (∃⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
      θ.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1])) 🡒
    ∃⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
      (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift.bShift ⋏
        θ.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1])))

@[simp] theorem collectionBody_shift (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    (collectionBody θ a t).shift=collectionBody θ.shift a.shift t.shift := by
  simp [collectionBody,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem collectionAt_shift (θ : Semiformula V ℒₛₑₜ 2) (a t c : Term V ℒₛₑₜ) :
    (collectionAt θ a t c).shift=collectionAt θ.shift a.shift t.shift c.shift := by
  simp [collectionAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem collectionBody_free (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    (collectionBody θ a t).free=collectionAt θ.shift a.shift t.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [Bootstrapping.Semiformula.free,collectionAt]
@[simp] theorem collectionConclusion_shift (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    (collectionConclusion θ a t).shift=collectionConclusion θ.shift a.shift t.shift := by
  simp [collectionConclusion,memTerm]
private theorem collectionAt_eq (θ : Semiformula V ℒₛₑₜ 2) (a t c : Term V ℒₛₑₜ) :
    collectionAt θ a t c=(memTerm t c ⋏ (supportAll θ t c ⋏ coverageAll θ a t c)) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [collectionAt,collectionBody,supportAll,coverageAll,memTerm,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

private theorem collection_support_all (θ : Semiformula V ℒₛₑₜ 2) (a t E r c : Term V ℒₛₑₜ) :
    Source V ⊢ collectionCondition θ a t E r c 🡒 supportAll θ t c := by
  unfold supportAll
  apply all_under
  have h := support_under θ.shift a.shift t.shift E.shift r.shift c.shift (Bootstrapping.Semiterm.fvar 0)
  simpa [supportImage,collectionCondition_shift,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail,←Bootstrapping.Semiterm.bShift_shift_comm] using h

private theorem collection_coverage_all (θ : Semiformula V ℒₛₑₜ 2) (a t E r c : Term V ℒₛₑₜ) :
    Source V ⊢ collectionCondition θ a t E r c 🡒 coverageAll θ a t c := by
  unfold coverageAll
  apply all_under
  have h := selected_under θ.shift a.shift t.shift E.shift r.shift c.shift (Bootstrapping.Semiterm.fvar 0)
  simpa [givenImage,selectedImage,collectionCondition_shift,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail,←Bootstrapping.Semiterm.bShift_shift_comm] using h

private theorem collection_exact (θ : Semiformula V ℒₛₑₜ 2) (a t E r c : Term V ℒₛₑₜ) :
    Source V ⊢ collectionCondition θ a t E r c 🡒 collectionAt θ a t c := by
  rw [collectionAt_eq]
  have ht := collection_tag θ E t r c
  have hs := collection_support_all θ a t E r c
  have hc := collection_coverage_all θ a t E r c
  unfold collectionCondition at hs hc ⊢
  cl_prover [ht,hs,hc]

attribute [local irreducible] collectionBody collectionAt collectionConclusion supportAll coverageAll

private theorem collection_of_roots (θ : Semiformula V ℒₛₑₜ 2) (a t E r : Term V ℒₛₑₜ) :
    Source V ⊢ (envelopeCondition a t E ⋏ rootCondition E t r) 🡒 ∃⁰ collectionBody θ a t := by
  apply deduct'!
  let H := envelopeCondition a t E ⋏ rootCondition E t r
  have h : [H] ⊢[Source V]
      (∃⁰ pairExists (collectionMatrix θ E t r) r) 🡒 ∃⁰ collectionBody θ a t := by
    apply TProof.exs_imp_exs!
    rw [pairExists_free,collectionBody_free,collectionMatrix_shift]
    have hp := FiniteContext.of'! (Γ := [H].map Bootstrapping.Semiformula.shift)
      (collection_exact θ.shift a.shift t.shift E.shift r.shift (Bootstrapping.Semiterm.fvar 0))
    have hH : [H].map Bootstrapping.Semiformula.shift ⊢[Source V]
        envelopeCondition a.shift t.shift E.shift ⋏ rootCondition E.shift t.shift r.shift := by
      simp only [H,List.map_cons,List.map_nil,Bootstrapping.Semiformula.shift_and,
        envelopeCondition_shift,rootCondition_shift]; exact by_axm₀!
    unfold collectionCondition at hp
    cl_prover [hp,hH]
  have hx := FiniteContext.of'! (Γ := [H]) (pair_exists (collectionMatrix θ E t r) r)
  exact ⟨h.get ⨀ hx.get⟩

private theorem collection_of_envelope (θ : Semiformula V ℒₛₑₜ 2) (a t E : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition a t E 🡒 ∃⁰ collectionBody θ a t := by
  have he : Source V ⊢ (∃⁰ rawPairBody E t) 🡒
      (envelopeCondition a t E 🡒 ∃⁰ collectionBody θ a t) := by
    apply exists_elim
    rw [rawPairBody_free]
    have hp := collection_of_roots θ.shift a.shift t.shift E.shift (Bootstrapping.Semiterm.fvar 0)
    have hn := envelope_ne a.shift t.shift E.shift
    unfold rootCondition at hp
    have h : Source V ⊢ rawPairAt E.shift t.shift (Bootstrapping.Semiterm.fvar 0) 🡒
        envelopeCondition a.shift t.shift E.shift 🡒 ∃⁰ collectionBody θ.shift a.shift t.shift := by
      unfold envelopeCondition at hp hn ⊢
      cl_prover [hp,hn]
    simpa only [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      envelopeCondition_shift,collectionBody_shift] using h
  exact ⟨he.get ⨀ (raw_pair E t).get⟩

/-- Exact tagged global-image Collection, with just Empty(t) and t∈a as
source antecedents. All matrix codes and free parameters may be internal. -/
theorem tagged_collection (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 memTerm t a 🡒 ∃⁰ collectionBody θ a t := by
  have he : Source V ⊢ (∃⁰ rawAugBody (tagMatrix t) a) 🡒
      (emptyAt t 🡒 memTerm t a 🡒 ∃⁰ collectionBody θ a t) := by
    apply exists_elim
    rw [rawAugBody_free,tagMatrix_shift]
    have hp := collection_of_envelope θ.shift a.shift t.shift (Bootstrapping.Semiterm.fvar 0)
    unfold envelopeCondition at hp
    simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      emptyAt_shift,memTerm,collectionBody_shift] using
      (show Source V ⊢ rawAugAt (tagMatrix t.shift) a.shift (Bootstrapping.Semiterm.fvar 0) 🡒
        emptyAt t.shift 🡒 memTerm t.shift a.shift 🡒 ∃⁰ collectionBody θ.shift a.shift t.shift from by
          cl_prover [hp])
  exact ⟨he.get ⨀ (raw_augmented (tagMatrix t) a).get⟩

def taggedCollectionProof (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    Source V ⊢! collectionConclusion θ a t := by
  simpa only [collectionConclusion] using (tagged_collection θ a t).get

theorem taggedCollectionProof_isProof (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    Proof seedTheory (taggedCollectionProof θ a t).val (collectionConclusion θ a t).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (taggedCollectionProof θ a t).derivationOf

/-! Fixed total raw syntax graphs. No whole proof-search graph is asserted. -/
private def eqMeta : SetTheorySemiproposition 2 :=
  FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#1]
private def singMeta : SetTheorySemiproposition 2 :=
  ∀⁰ (seedMem 3 0 2 🡘 FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#1])
private def eqCode : ℕ := ⌜eqMeta⌝
private def memCode : ℕ := ⌜seedMem 2 0 1⌝
private def singCode : ℕ := ⌜singMeta⌝
private def b0Code : ℕ := ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 2)⌝
private def b1Code : ℕ := ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 2)⌝
private def b2Code : ℕ := ⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝
private def mem02Code : ℕ := ⌜seedMem 3 0 2⌝
private def at2Code (u v k : V) : V := subst ℒₛₑₜ (u∷v∷0) k
private def at2Graph : 𝚺₁.Semisentence 4 := .mkSigma
  “out u v k. ∃ tail vec, !adjoinDef tail v 0 ∧ !adjoinDef vec u tail ∧
    !(Bootstrapping.substsGraph ℒₛₑₜ) out vec k”
private instance at2_defined : 𝚺₁-Function₃ (at2Code : V→V→V→V) via at2Graph :=
  .mk fun v => by simp [at2Graph,at2Code]
private lemma b0_cast : (b0Code : V)=(^#0 : V) := by
  rw [b0Code,FirstOrder.Semiterm.coe_quote_eq_quote]
  rfl
private lemma b1_cast : (b1Code : V)=(^#1 : V) := by
  rw [b1Code,FirstOrder.Semiterm.coe_quote_eq_quote]
  simp [FirstOrder.Semiterm.quote_def]
private lemma eq_cast : (eqCode : V)=(⌜eqMeta⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote eqMeta
private lemma mem_cast : (memCode : V)=(⌜seedMem 2 0 1⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote (seedMem 2 0 1)
private lemma sing_cast : (singCode : V)=(⌜singMeta⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote singMeta

private theorem at2_eq {n : ℕ} (u v : Semiterm V ℒₛₑₜ n) :
    at2Code u.val v.val eqCode=(eqTerm u v).val := by
  rw [eq_cast]
  change (((⌜eqMeta⌝ : Semiformula V ℒₛₑₜ 2).subst ![u,v]).val)=(eqTerm u v).val
  congr 1
  simp [eqMeta,eqTerm,Matrix.vecHead,Matrix.vecTail]
private theorem at2_mem {n : ℕ} (u v : Semiterm V ℒₛₑₜ n) :
    at2Code u.val v.val memCode=(memTerm u v).val := by
  rw [mem_cast]
  change (((⌜seedMem 2 0 1⌝ : Semiformula V ℒₛₑₜ 2).subst ![u,v]).val)=(memTerm u v).val
  congr 1
  simp [seedMem,memTerm,Matrix.vecHead,Matrix.vecTail]

private lemma b2_cast : (b2Code : V)=(^#2 : V) := by
  rw [b2Code,FirstOrder.Semiterm.coe_quote_eq_quote]
  simp [FirstOrder.Semiterm.quote_def]
private lemma mem02_cast : (mem02Code : V)=(⌜seedMem 3 0 2⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote (seedMem 3 0 2)

/-- Total raw constructor; the ambient parameters are term codes. -/
def collectionMatrixCode (k E t r : V) : V :=
  (at2Code b1Code r eqCode ^⋏ at2Code b0Code E eqCode) ^⋎
    ((at2Code b1Code t eqCode ^⋏ at2Code b0Code t eqCode) ^⋎
      ^∃ (at2Code t b0Code memCode ^⋏
        (at2Code b0Code b2Code singCode ^⋏
          (at2Code t b1Code memCode ^⋏ at2Code b1Code b0Code k))))
def collectionBodyCode (k a t : V) : V :=
  at2Code t b0Code memCode ^⋏
    ((^∀ (Bootstrapping.imp ℒₛₑₜ (at2Code t b0Code memCode)
      (Bootstrapping.imp ℒₛₑₜ memCode
        (^∃ (at2Code t b0Code memCode ^⋏ at2Code b1Code b0Code k))))) ^⋏
    (^∀ (Bootstrapping.imp ℒₛₑₜ (at2Code t b0Code memCode)
      (Bootstrapping.imp ℒₛₑₜ (at2Code b0Code a memCode)
        (Bootstrapping.imp ℒₛₑₜ
          (^∃ (at2Code t b0Code memCode ^⋏ at2Code b0Code b1Code k))
          (^∃ (at2Code t b0Code memCode ^⋏ (mem02Code ^⋏ at2Code b0Code b1Code k))))))))
def collectionConclusionCode (k a t : V) : V :=
  Bootstrapping.imp ℒₛₑₜ
    (^∀ (Bootstrapping.imp ℒₛₑₜ (at2Code b0Code t memCode) ^⊥))
    (Bootstrapping.imp ℒₛₑₜ (at2Code t a memCode) (^∃ (collectionBodyCode k a t)))

def collectionMatrixGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out k E t r. ∃ er eE et et' tagx sing tagy th root empty tail chosen body image right,
    !at2Graph er ↑b1Code r ↑eqCode ∧ !at2Graph eE ↑b0Code E ↑eqCode ∧
    !at2Graph et ↑b1Code t ↑eqCode ∧ !at2Graph et' ↑b0Code t ↑eqCode ∧
    !at2Graph tagx t ↑b0Code ↑memCode ∧ !at2Graph sing ↑b0Code ↑b2Code ↑singCode ∧
    !at2Graph tagy t ↑b1Code ↑memCode ∧ !at2Graph th ↑b1Code ↑b0Code k ∧
    !qqAndDef root er eE ∧ !qqAndDef empty et et' ∧ !qqAndDef tail tagy th ∧
    !qqAndDef chosen sing tail ∧ !qqAndDef body tagx chosen ∧ !qqExsDef image body ∧
    !qqOrDef right empty image ∧ !qqOrDef out root right”
def collectionBodyGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out k a t. ∃ tag ma th10 th01 imageBody image support' supportBody support
      givenBody given selectedTail selectedBody selected cover' cover'' coverBody cover both,
    !at2Graph tag t ↑b0Code ↑memCode ∧ !at2Graph ma ↑b0Code a ↑memCode ∧
    !at2Graph th10 ↑b1Code ↑b0Code k ∧ !at2Graph th01 ↑b0Code ↑b1Code k ∧
    !qqAndDef imageBody tag th10 ∧ !qqExsDef image imageBody ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) support' ↑memCode image ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) supportBody tag support' ∧ !qqAllDef support supportBody ∧
    !qqAndDef givenBody tag th01 ∧ !qqExsDef given givenBody ∧
    !qqAndDef selectedTail ↑mem02Code th01 ∧ !qqAndDef selectedBody tag selectedTail ∧
    !qqExsDef selected selectedBody ∧ !(Bootstrapping.impGraph ℒₛₑₜ) cover' given selected ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) cover'' ma cover' ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) coverBody tag cover'' ∧ !qqAllDef cover coverBody ∧
    !qqAndDef both support cover ∧ !qqAndDef out tag both”
def collectionConclusionGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out k a t. ∃ mt emptyBody empty tag body exbody consequent,
    !at2Graph mt ↑b0Code t ↑memCode ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) emptyBody mt ↑(Bootstrapping.qqFalsum : ℕ) ∧
    !qqAllDef empty emptyBody ∧ !at2Graph tag t a ↑memCode ∧
    !collectionBodyGraph body k a t ∧ !qqExsDef exbody body ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) consequent tag exbody ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) out empty consequent”

instance collectionMatrix_defined : 𝚺₁-Function₄[V] collectionMatrixCode via collectionMatrixGraph :=
  .mk fun v => by simp [collectionMatrixGraph,collectionMatrixCode,numeral_eq_natCast]
instance collectionBody_defined : 𝚺₁-Function₃[V] collectionBodyCode via collectionBodyGraph :=
  .mk fun v => by simp [collectionBodyGraph,collectionBodyCode,numeral_eq_natCast]
instance collectionConclusion_defined : 𝚺₁-Function₃[V] collectionConclusionCode via collectionConclusionGraph :=
  .mk fun v => by simp [collectionConclusionGraph,collectionConclusionCode,numeral_eq_natCast]

theorem collectionMatrixCode_eq (θ : Semiformula V ℒₛₑₜ 2) (E t r : Term V ℒₛₑₜ) :
    collectionMatrixCode θ.val E.val t.val r.val=(collectionMatrix θ E t r).val := by
  rcases term_is_fvar E with ⟨E,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  have hE := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar E)
  have ht0 := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar t)
  have ht1 := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar t)
  have hr := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar r)
  have htx := at2_mem (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.bvar (0 : Fin 3))
  have hty := at2_mem (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.bvar (1 : Fin 3))
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm,memTerm] at hE ht0 ht1 hr htx hty
  simp only [collectionMatrixCode,b0_cast,b1_cast,b2_cast,Bootstrapping.Semiterm.fvar,hE,ht0,ht1,hr,htx,hty]
  simp [collectionMatrix,at2Code,sing_cast,singMeta,seedMem,singTerm,eqTerm,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail]

theorem collectionBodyCode_eq (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    collectionBodyCode θ.val a.val t.val=(collectionBody θ a t).val := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  have hma := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
  have htag := at2_mem (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.bvar (0 : Fin 2))
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,memTerm] at hma htag
  simp only [collectionBodyCode,b0_cast,b1_cast,Bootstrapping.Semiterm.fvar,hma,htag]
  simp [collectionBody,at2Code,mem_cast,mem02_cast,seedMem,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.imp]

theorem collectionConclusionCode_eq (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    collectionConclusionCode θ.val a.val t.val=(collectionConclusion θ a t).val := by
  have hb := collectionBodyCode_eq θ a t
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  have hmt := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 1)) (Bootstrapping.Semiterm.fvar t)
  have hta := at2_mem (Bootstrapping.Semiterm.fvar t : Term V ℒₛₑₜ) (Bootstrapping.Semiterm.fvar a)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,memTerm] at hmt hta
  simp only [collectionConclusionCode,b0_cast,Bootstrapping.Semiterm.fvar,hmt,hta,hb]
  simp [collectionConclusion,emptyAt,memTerm,Bootstrapping.imp]

end LeanProofs.ZFCinPA.ValidatorSeedTaggedCollection222
