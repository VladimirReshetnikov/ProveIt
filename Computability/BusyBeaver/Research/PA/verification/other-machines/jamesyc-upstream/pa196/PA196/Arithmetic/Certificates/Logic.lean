module
public import M6PA.Theory
public import PA196.Arithmetic.Certificates.ImplicationBasis
@[expose] public section

/-! Finite schematic certificate recipes over arbitrary PA-model values.
Every closed result contains an explicit accepted PA196 numeric code. This finite
context datatype is not an internal source derivation predicate. -/
open M6.PA
namespace PA196.Arithmetic.Certificates.Logic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open Checker HeadGraphs

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable abbrev wn (a : V) : V := wim a 1
noncomputable abbrev wal (v a : V) : V := universalValue v a
noncomputable abbrev wa (a b : V) : V := wn (wim a (wn b))

noncomputable def _root_.PA196.Arithmetic.Certificates.Dominated.Certificate.mp {a b : V} (p : Certificate a) (q : Certificate (wim a b)) : Certificate b :=
  ⟨mpCertificate b p.code q.code,verify_mp _ _ _ _ p.accepted q.accepted⟩
noncomputable def _root_.PA196.Arithmetic.Certificates.Dominated.Certificate.all (v : V) {a : V} (p : Certificate a) : Certificate (wal v a) :=
  ⟨genCertificate v p.code,verify_gen _ _ _ p.accepted⟩

/-- The source's sixth head has its antecedents reversed. -/
noncomputable def r2 (v a b : V) : Certificate (wim (wal v (wim a b)) (wim (wal v a) (wal v b))) := by
  let raw : Certificate (wim (wal v a) (wim (wal v (wim a b)) (wal v b))) :=
    ⟨leafCertificate 7 (pack3Value v a b),by
      simpa [wim,wal,implicationValue,universalValue,head6Expr,
        M6.PA.ActualArithmeticGraph.eval,im,al,implicationExpr,universalExpr]
        using verify_head6 v a b⟩
  exact .mp raw (Dominated.exchange (wal v a) (wal v (wim a b)) (wal v b))

noncomputable def r6 (v a : V) : Certificate (wim (wn (wal v (wn (wal v a)))) a) :=
  ⟨leafCertificate 2 (pack2Value v a),by
    simpa [wim,wn,wal,implicationValue,universalValue,head1Expr,
      M6.PA.ActualArithmeticGraph.eval,im,al,ex,neg,implicationExpr,universalExpr]
      using verify_head1 v a⟩

noncomputable def identity (a : V) : Certificate (wim a a) :=
  .mp (Dominated.k a a)
    (.mp (Dominated.k a (wim a a)) (Dominated.s a (wim a a) a))

inductive Context (Γ : List V) : V → Type u where
  | assumption {a} : a ∈ Γ → Context Γ a
  | closed {a} : Certificate a → Context Γ a
  | mp {a b} : Context Γ a → Context Γ (wim a b) → Context Γ b

noncomputable def Context.cut {Γ Δ : List V} {a : V} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Context Δ b) : Context Δ a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => .closed p
  | .mp p q => .mp (p.cut subst) (q.cut subst)

noncomputable def Context.close {Γ : List V} {a : V} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Certificate b) : Certificate a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => p
  | .mp p q => .mp (p.close subst) (q.close subst)

noncomputable def Context.empty {a : V} (d : Context [] a) : Certificate a :=
  d.close (fun _ h => False.elim (List.not_mem_nil h))

noncomputable def Context.lift {Γ : List V} {a : V} (d : Context Γ a) (h : V) :
    Context Γ (wim h a) := .mp d (.closed (Dominated.k a h))

noncomputable def Context.deduction {Γ : List V} {h a : V} (d : Context (h :: Γ) a) :
    Context Γ (wim h a) :=
  match d with
  | .assumption ha => by
    classical
    by_cases e : a = h
    · subst a
      exact .closed (identity h)
    · exact (Context.assumption ((List.mem_cons.mp ha).resolve_left e)).lift h
  | .closed p => (Context.closed p).lift h
  | .mp (a := b) p q => .mp p.deduction (.mp q.deduction (.closed (Dominated.s h b a)))

noncomputable def Context.explosion {Γ : List V} (a : V) (d : Context Γ 1) : Context Γ a :=
  .mp (.mp d (.closed (Dominated.k 1 (wal 0 (wn (wal 0 a)))))) (.closed (r6 0 a))

noncomputable def explosion (a : V) : Certificate (wim 1 a) :=
  ((Context.assumption (Γ := [(1:V)]) (by simp) : Context [(1:V)] (1:V)).explosion a).deduction.empty

noncomputable def doubleNegationElimination (a : V) : Certificate (wim (wn (wn a)) a) := by
  let p : Context [wn a, wn (wn a)] (wn a) := .assumption (by simp)
  let q : Context [wn a, wn (wn a)] (wn (wn a)) := .assumption (by simp)
  let contradiction : Context [wn a, wn (wn a)] 1 := .mp p q
  let conditional : Context [wn (wn a)] (wim (wn a) a) :=
    (contradiction.explosion a).deduction
  exact (Context.mp conditional (.closed (Dominated.peirce a 1))).deduction.empty

#print axioms identity
#print axioms Context.deduction
#print axioms explosion
#print axioms doubleNegationElimination




noncomputable def Context.up {Γ : List V} {a : V} (p : Context Γ a) (h : V) :
    Context (h :: Γ) a := p.cut (fun _ hb => .assumption (List.mem_cons_of_mem h hb))

noncomputable def Context.dne {Γ : List V} {a : V} (p : Context Γ (wn (wn a))) : Context Γ a :=
  .mp p (.closed (doubleNegationElimination a))

noncomputable def Context.andIntro {Γ : List V} {a b : V} (p : Context Γ a) (q : Context Γ b) :
    Context Γ (wa a b) :=
  (Context.mp (q.up (wim a (wn b)))
    (.mp (p.up (wim a (wn b))) (.assumption (by simp [wn])))).deduction

noncomputable def Context.andLeft {Γ : List V} {a b : V} (p : Context Γ (wa a b)) : Context Γ a := by
  let ha : Context (a :: wn a :: Γ) a := .assumption (by simp)
  let hn : Context (a :: wn a :: Γ) (wn a) := .assumption (by simp)
  let arrow : Context (wn a :: Γ) (wim a (wn b)) :=
    ((Context.mp ha hn).explosion (wn b)).deduction
  exact (Context.mp arrow (p.up (wn a))).deduction.dne

noncomputable def Context.andRight {Γ : List V} {a b : V} (p : Context Γ (wa a b)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  exact (Context.mp (hn.lift a) (p.up (wn b))).deduction.dne

noncomputable def contraposition (a b : V) : Certificate (wim (wim a b) (wim (wn b) (wn a))) := by
  let pa : Context [a, wn b, wim a b] a := .assumption (by simp)
  let pab : Context [a, wn b, wim a b] (wim a b) := .assumption (by simp)
  let pnb : Context [a, wn b, wim a b] (wn b) := .assumption (by simp)
  exact (Context.mp (.mp pa pab) pnb).deduction.deduction.deduction.empty

noncomputable def contrapose {a b : V} (p : Certificate (wim a b)) : Certificate (wim (wn b) (wn a)) :=
  .mp p (contraposition a b)

noncomputable def implicationCompose {a b c : V} (p : Certificate (wim a b))
    (q : Certificate (wim b c)) : Certificate (wim a c) :=
  .mp q (.mp p (Dominated.composition a b c))


#print axioms Certificate.mp
#print axioms Certificate.all
#print axioms r2
#print axioms r6
#print axioms contraposition
#print axioms contrapose
#print axioms implicationCompose
end PA196.Arithmetic.Certificates.Logic

