import PA194ConditionalSingleton
import PA194InternalBitDiagonalTerm
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194EqualGateWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ConditionalSingleton PA194ConditionalSingletonLogic
open DiophantineConsistency
section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def relConj {n : Nat} (A B D : Bootstrapping.Semiformula V ℒₒᵣ n) := (A 🡒 B 🡒 D) 🡒 D

lemma conj_with_diag (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (B : Bootstrapping.Semiformula V ℒₒᵣ 2)
    (D : Bootstrapping.Semiformula V ℒₒᵣ 1) (z : V)
    (hdiag : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∀⁰ ∼(B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0])) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P)) 🡒
      ∀⁰ (relConj
        ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0]) 🡒
          (P 🡒 (B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z])))
        ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P) D) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let R : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
    (B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P
  let Q : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
    relConj ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0]) 🡒
      (P 🡒 (B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]))) R D
  change T ⊢ (∀⁰ R) 🡒 ∀⁰ Q
  apply Nonempty.intro
  apply TProof.generalizeAux
  apply FiniteContext.deduct'
  have hu : [(∀⁰ R).shift] ⊢[T]! ∀⁰ R.shift := by
    simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ R).shift] ⊢[T]! (∀⁰ R).shift)
  have hr : [(∀⁰ R).shift] ⊢[T]! R.free := by
    simpa [Bootstrapping.Semiformula.free] using TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
  have hd : [(∀⁰ R).shift] ⊢[T]! ∀⁰ (∼(B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0])).shift := by
    simpa using (FiniteContext.of (TProof.shift hdiag.some) : [(∀⁰ R).shift] ⊢[T]! (∀⁰ ∼(B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0])).shift)
  have hn := TProof.specializeWithCtx hd (Bootstrapping.Semiterm.fvar 0)
  let Diag : Bootstrapping.Formula V ℒₒᵣ := B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar 0]
  let Point : Bootstrapping.Formula V ℒₒᵣ := P.free 🡒 B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar (z+1)]
  let A := Diag 🡒 Point
  have hn' : [(∀⁰ R).shift] ⊢[T]! ∼Diag := by
    simpa [Diag, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using hn
  have hprop : [(∀⁰ R).shift] ⊢[T]! ∼Diag 🡒 Diag 🡒 Point := CNC
  have hA : [(∀⁰ R).shift] ⊢[T]! A := hprop ⨀ hn'
  have ht : T ⊢! A 🡒 R.free 🡒 ((A 🡒 R.free 🡒 D.free) 🡒 D.free) := by
    apply FiniteContext.deduct'
    apply FiniteContext.deduct
    apply FiniteContext.deduct
    have hx : [A 🡒 R.free 🡒 D.free, R.free, A] ⊢[T]! A 🡒 R.free 🡒 D.free := FiniteContext.byAxm (by simp)
    have ha : [A 🡒 R.free 🡒 D.free, R.free, A] ⊢[T]! A := FiniteContext.byAxm (by simp)
    have hb : [A 🡒 R.free 🡒 D.free, R.free, A] ⊢[T]! R.free := FiniteContext.byAxm (by simp)
    exact hx ⨀ ha ⨀ hb
  have hres : [(∀⁰ R).shift] ⊢[T]! relConj A R.free D.free := FiniteContext.of ht ⨀ hA ⨀ hr
  simpa [Q,R,relConj,A,Point,Diag,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail] using hres
lemma bit_template_shift :
    (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift =
      (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) := by
  rw [← Semiformula.typed_quote_shift]
  congr 1
  change Rew.shift ▹ (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) = _
  apply Semiformula.rew_eq_self_of
  · intro x; simp
  · intro x hx
    exfalso
    have he : (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2).freeVariables = ∅ := Semiformula.freeVariables_emb bitDef.val
    change x ∈ (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2).freeVariables at hx
    rw [he] at hx
    simpa using hx

lemma bit_irreflexive_all : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ ∼(Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 0)) := by
  apply TProof.all!
  have h := PA194InternalBitDiagonalTerm.internal_PA_proves_bit_diag_neg_term (Bootstrapping.Semiterm.fvar (0 : V))
  simpa [PA194ConditionalSingleton.Bit,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs, bit_template_shift, Matrix.vecHead,Matrix.vecTail] using h

noncomputable def collisionBody (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (D : Bootstrapping.Semiformula V ℒₒᵣ 2) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ((P.subst ![Bootstrapping.Semiterm.fvar a]).subst ![] 🡒
    PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.bvar 0)) ⋏
  (∀⁰ relConj
    ((PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 0)) 🡒
      ((P.subst ![Bootstrapping.Semiterm.bvar 0]) 🡒
        PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)))
    ((PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) 🡒
      P.subst ![Bootstrapping.Semiterm.bvar 0]) D)

lemma collision_witness (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (D : Bootstrapping.Semiformula V ℒₒᵣ 2) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ collisionBody a P D := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let W := desiredBody a P
  let S := collisionBody a P D
  have hw : T ⊢ ∃⁰ W := conditional_singleton a P
  have hi : T ⊢! (∃⁰ W) 🡒 ∃⁰ S := by
    apply FiniteContext.emptyPrf
    apply TProof.exsImpExs
    simp only [List.map_nil]
    apply FiniteContext.deduct
    have h : [W.free] ⊢[T]! W.free := FiniteContext.byAxm (by simp)
    simp only [W,desiredBody,Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_and, Bootstrapping.Semiformula.substs_and] at h
    have hl := K_left h
    have hr := K_right h
    simp only [S,collisionBody,Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_and, Bootstrapping.Semiformula.substs_and]
    apply K_intro
    · simpa [W,S,desiredBody,collisionBody,Bootstrapping.Semiformula.free] using hl
    · let B : Bootstrapping.Semiformula V ℒₒᵣ 2 :=
        (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift
      let D' : Bootstrapping.Semiformula V ℒₒᵣ 1 := D.shift.subst (SemitermVec.q ![Bootstrapping.Semiterm.fvar 0])
      have hdiag : T ⊢ ∀⁰ ∼(B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0]) := by
        simpa [B,PA194ConditionalSingleton.Bit,bit_template_shift] using (bit_irreflexive_all (V := V))
      have hh := conj_with_diag P.shift B D' 0 hdiag
      have hh' : [W.free] ⊢[T]! (∀⁰ ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar 0]) 🡒 P.shift)) 🡒
        ∀⁰ (relConj ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0]) 🡒
          (P.shift 🡒 B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar 0]))
          ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar 0]) 🡒 P.shift) D') := FiniteContext.of hh.some
      have hr' : [W.free] ⊢[T]! ∀⁰ ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar 0]) 🡒 P.shift) := by
        simpa [W,desiredBody,PA194ConditionalSingleton.Bit,B, Bootstrapping.Semiformula.free,
          Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
          SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hr
      have hs := hh' ⨀ hr'
      simpa [S,collisionBody,PA194ConditionalSingleton.Bit,B,D',relConj, Bootstrapping.Semiformula.free,
        Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
        SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hs
  exact ⟨hi ⨀ hw.some⟩

lemma tail_from_witness (Point Sep E : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (C : Bootstrapping.Formula V ℒₒᵣ)
    (hW : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ (Point ⋏ Sep))
    (hE : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰ ∼E) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 C := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  have himp : T ⊢! (∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 ∀⁰ ∼(Point ⋏ Sep) := by
    apply FiniteContext.emptyPrf
    apply TProof.allImpAll
    simp only [List.map_nil]
    have hshift : T ⊢! ∀⁰ (∼E).shift := by simpa using TProof.shift hE.some
    have hn : [] ⊢[T]! ∼E.free := by
      have hs := TProof.specializeWithCtx (FiniteContext.of hshift : [] ⊢[T]! ∀⁰ (∼E).shift) (Bootstrapping.Semiterm.fvar 0)
      simpa [Bootstrapping.Semiformula.free] using hs
    apply FiniteContext.deduct
    have ht : [((Sep 🡒 Point 🡒 E).free)] ⊢[T]! Sep.free 🡒 Point.free 🡒 E.free := by
      simpa [Bootstrapping.Semiformula.free] using
        (FiniteContext.byAxm (by simp) : [((Sep 🡒 Point 🡒 E).free)] ⊢[T]! (Sep 🡒 Point 🡒 E).free)
    have hn' : [((Sep 🡒 Point 🡒 E).free)] ⊢[T]! ∼E.free := FiniteContext.weakening (by simp) hn
    have ht' : [((Sep 🡒 Point 🡒 E).free)] ⊢[T]! (Point.free ⋏ Sep.free) 🡒 E.free := by
      apply FiniteContext.deduct
      have hc : [(Point.free ⋏ Sep.free), (Sep 🡒 Point 🡒 E).free] ⊢[T]! Point.free ⋏ Sep.free := FiniteContext.byAxm (by simp)
      have htail : [(Point.free ⋏ Sep.free), (Sep 🡒 Point 🡒 E).free] ⊢[T]! Sep.free 🡒 Point.free 🡒 E.free :=
        FiniteContext.weakening (by simp) ht
      exact htail ⨀ K_right hc ⨀ K_left hc
    have hc := contra ht' ⨀ hn'
    simpa [Bootstrapping.Semiformula.free] using hc
  have hnot : T ⊢! ∼(∀⁰ (Sep 🡒 Point 🡒 E)) := by
    have hh : T ⊢! (∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 ∼(∃⁰ (Point ⋏ Sep)) := by simpa using himp
    exact CN_of_CN_right hh ⨀ hW.some
  have hlogic : T ⊢! ∼(∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 (∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 C := CNC
  exact ⟨hlogic ⨀ hnot⟩

#print axioms tail_from_witness
#print axioms collision_witness
#print axioms bit_irreflexive_all
#print axioms conj_with_diag
end model
end PA194EqualGateWitness
