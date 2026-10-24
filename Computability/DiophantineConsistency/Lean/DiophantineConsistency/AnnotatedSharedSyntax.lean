import DiophantineConsistency.AnnotatedSyntaxGraphs

/-! # Shared quadratic rows for every fixed tree/formula constructor -/
namespace DiophantineConsistency.AnnotatedSharedSyntax
open AnnotatedProofCode AnnotatedSyntaxGraphs AnnotatedRename
open NaturalRegisterProgram QuadraticRegisterSystem
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

def width : Tree → Nat
  | .atom _ => 0
  | .fork a b => 4+width a+width b


theorem width_eq (t : Tree) : width t=4*forkCount t := by
  induction t with
  | atom n => rfl
  | fork a b ha hb => simp only [width,forkCount]; omega

def centerIndex (a b : Tree) (i : Fin 4) : Fin (width (.fork a b)) :=
  Fin.castAdd (width b) (Fin.castAdd (width a) i)
def leftIndex (a b : Tree) (i : Fin (width a)) : Fin (width (.fork a b)) :=
  Fin.castAdd (width b) (Fin.natAdd 4 i)
def rightIndex (a b : Tree) (i : Fin (width b)) : Fin (width (.fork a b)) :=
  Fin.natAdd (4+width a) i

def assemble (a b : Tree) (center : Fin 4 → Nat) (left : Fin (width a) → Nat)
    (right : Fin (width b) → Nat) : Fin (width (.fork a b)) → Nat :=
  Fin.addCases (Fin.addCases center left) right

@[simp] theorem assemble_center (a b : Tree) (center : Fin 4 → Nat) (left right) (i : Fin 4) :
    assemble a b center left right (centerIndex a b i)=center i := by
  simp only [assemble,centerIndex,Fin.addCases_left]
@[simp] theorem assemble_left (a b : Tree) (center left right) (i : Fin (width a)) :
    assemble a b center left right (leftIndex a b i)=left i := by
  simp only [assemble,leftIndex,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem assemble_right (a b : Tree) (center left right) (i : Fin (width b)) :
    assemble a b center left right (rightIndex a b i)=right i := by
  simp only [assemble,rightIndex,Fin.addCases_right]

/-- The stored output of a fork; an atom is computed directly from its label. -/
def rootExpression : (t : Tree) → Expr (Fin (width t))
  | .atom n => .constant (n:ℤ)*.constant (n:ℤ)+1
  | .fork a b => .var (centerIndex a b 0)

def rootValue : (t : Tree) → (Fin (width t) → Nat) → Nat
  | .atom n,_ => (Tree.atom n).quote
  | .fork a b,w => w (centerIndex a b 0)

private theorem zero_pair (n : Nat) : Nat.pair 0 n=n*n := by
  cases n with
  | zero => rfl
  | succ n => simp [Nat.pair]

@[simp] theorem rootExpression_eval (t : Tree) (w : Fin (width t) → Nat) :
    (rootExpression t).eval (fun i => (w i:ℤ))=(rootValue t w:ℤ) := by
  cases t with
  | atom n => simp [rootExpression,rootValue,Expr.eval,Tree.quote,zero_pair]
  | fork a b => rfl

private theorem syntaxDegree_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    syntaxDegree (e.rename f)=syntaxDegree e := by
  induction e <;> simp_all [Expr.rename,syntaxDegree]

theorem rootExpression_degree (t : Tree) : syntaxDegree (rootExpression t)≤1 := by
  cases t <;> simp [rootExpression,syntaxDegree]

def localResiduals {σ : Type*} (out a b bit slack maximum : Expr σ) : Fin 4 → Expr σ :=
  Fin.cases (bit*(bit-1))
    (Fin.cases (maximum-((1-bit)*b+bit*(a+1)))
      (Fin.cases (b+bit*slack-(a+1)-(1-bit)*(slack+1))
        (Fin.cases (out-1-maximum*maximum-(a+1)-bit*b) (fun i => Fin.elim0 i))))

@[simp] private theorem degree_add {σ : Type*} (a b : Expr σ) :
    syntaxDegree (a+b)=max (syntaxDegree a) (syntaxDegree b) := rfl
@[simp] private theorem degree_sub {σ : Type*} (a b : Expr σ) :
    syntaxDegree (a-b)=max (syntaxDegree a) (syntaxDegree b) := rfl
@[simp] private theorem degree_mul {σ : Type*} (a b : Expr σ) :
    syntaxDegree (a*b)=syntaxDegree a+syntaxDegree b := rfl
@[simp] private theorem degree_one {σ : Type*} : syntaxDegree (1 : Expr σ)=0 := rfl

private theorem localResiduals_degree {σ : Type*} (out a b bit slack maximum : Expr σ)
    (ho : syntaxDegree out≤1) (ha : syntaxDegree a≤1) (hb : syntaxDegree b≤1)
    (ht : syntaxDegree bit≤1) (hs : syntaxDegree slack≤1) (hm : syntaxDegree maximum≤1)
    (i : Fin 4) : syntaxDegree (localResiduals out a b bit slack maximum i)≤2 := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun z => z.elim0)))) i
  all_goals simp only [localResiduals,Fin.cases_zero,Fin.cases_succ,degree_add,degree_sub,degree_mul,degree_one]; omega

/-- Four local rows and the two renamed child row blocks; every row remains
quadratic in one common witness scope. -/
def residual : (t : Tree) → Fin (width t) → Expr (Fin (width t))
  | .atom _ => fun i => Fin.elim0 i
  | .fork a b =>
    Fin.addCases
      (Fin.addCases
        (localResiduals (.var (centerIndex a b 0))
          ((rootExpression a).rename (leftIndex a b)) ((rootExpression b).rename (rightIndex a b))
          (.var (centerIndex a b 1)) (.var (centerIndex a b 2)) (.var (centerIndex a b 3)))
        (fun i => (residual a i).rename (leftIndex a b)))
      (fun i => (residual b i).rename (rightIndex a b))

def Valid (t : Tree) (w : Fin (width t) → Nat) : Prop :=
  ∀ i,(residual t i).eval (fun j => (w j:ℤ))=0

theorem valid_fork_iff (a b : Tree) (w : Fin (width (.fork a b)) → Nat) :
    Valid (.fork a b) w ↔
      ForkCertificate (w (centerIndex a b 0)) (rootValue a (w ∘ leftIndex a b))
        (rootValue b (w ∘ rightIndex a b)) (w (centerIndex a b 1))
        (w (centerIndex a b 2)) (w (centerIndex a b 3)) ∧
      Valid a (w ∘ leftIndex a b) ∧ Valid b (w ∘ rightIndex a b) := by
  simp only [Valid,width,residual,Fin.forall_fin_add,Fin.addCases_left,Fin.addCases_right,
    Expr.eval_rename,Function.comp_def]
  have hl : (∀ i : Fin 4,(localResiduals (.var (centerIndex a b 0))
      ((rootExpression a).rename (leftIndex a b)) ((rootExpression b).rename (rightIndex a b))
      (.var (centerIndex a b 1)) (.var (centerIndex a b 2)) (.var (centerIndex a b 3)) i).eval
      (fun j => (w j:ℤ))=0) ↔
      ForkCertificate (w (centerIndex a b 0)) (rootValue a (w ∘ leftIndex a b))
        (rootValue b (w ∘ rightIndex a b)) (w (centerIndex a b 1))
        (w (centerIndex a b 2)) (w (centerIndex a b 3)) := by
    simp [Fin.forall_fin_succ,localResiduals,Expr.eval,Expr.eval_rename,rootExpression_eval,
      ForkCertificate,Function.comp_def]
  erw [hl]
  exact and_assoc

theorem rootValue_sound (t : Tree) (w : Fin (width t) → Nat) (h : Valid t w) : rootValue t w=t.quote := by
  induction t with
  | atom n => rfl
  | fork a b ha hb =>
    obtain ⟨hc,hleft,hright⟩ := (valid_fork_iff a b w).mp h
    have ho := forkCertificate_sound hc
    rw [ha _ hleft,hb _ hright] at ho
    exact ho

theorem valid_exists (t : Tree) : ∃ w : Fin (width t) → Nat,Valid t w := by
  induction t with
  | atom n => exact ⟨Fin.elim0,fun i => i.elim0⟩
  | fork a b ha hb =>
    obtain ⟨left,hl⟩ := ha
    obtain ⟨right,hr⟩ := hb
    obtain ⟨bit,slack,maximum,hc⟩ := forkCertificate_complete (a:=a.quote) (b:=b.quote) rfl
    let center : Fin 4 → Nat := ![forkCode a.quote b.quote,bit,slack,maximum]
    refine ⟨assemble a b center left right,(valid_fork_iff a b _).mpr ?_⟩
    have heLeft : assemble a b center left right ∘ leftIndex a b=left := by funext i; simp
    have heRight : assemble a b center left right ∘ rightIndex a b=right := by funext i; simp
    rw [heLeft,heRight]
    refine ⟨?_,hl,hr⟩
    simp only [assemble_center,rootValue_sound a left hl,rootValue_sound b right hr]
    exact hc

theorem residual_degree (t : Tree) (i : Fin (width t)) : syntaxDegree (residual t i)≤2 := by
  induction t with
  | atom n => exact i.elim0
  | fork a b ha hb =>
    refine Fin.addCases (fun j : Fin (4+width a) => ?_) (fun j : Fin (width b) => ?_) i
    · refine Fin.addCases (fun k : Fin 4 => ?_) (fun k : Fin (width a) => ?_) j
      · simp only [residual,Fin.addCases_left]
        apply localResiduals_degree
        · exact Nat.le_refl 1
        · rw [syntaxDegree_rename]; exact rootExpression_degree a
        · rw [syntaxDegree_rename]; exact rootExpression_degree b
        · exact Nat.le_refl 1
        · exact Nat.le_refl 1
        · exact Nat.le_refl 1
      · simpa only [residual,Fin.addCases_left,Fin.addCases_right,syntaxDegree_rename] using ha k
    · simpa only [residual,Fin.addCases_right,syntaxDegree_rename] using hb j

/-- One common natural scope: claimed output followed by all stored fork
outputs and their three local auxiliaries. No arithmetic gate registers or
quoted-numeral constants are introduced. -/
def program (t : Tree) : Program (1+width t) := .empty

def tail (t : Tree) (x : Fin (1+width t) → Nat) : Fin (width t) → Nat :=
  fun i => x (Fin.natAdd 1 i)

def equations (t : Tree) : Fin (1+width t) →
    Expr (Fin (1+width t) ⊕ Fin (program t).nodes.length) :=
  Fin.addCases
    (fun _ : Fin 1 => .var (.inl 0) -
      (rootExpression t).rename (fun i => .inl (Fin.natAdd 1 i)))
    (fun i => (residual t i).rename (fun j => .inl (Fin.natAdd 1 j)))

theorem equations_degree (t : Tree) (i : Fin (1+width t)) : syntaxDegree (equations t i)≤2 := by
  refine Fin.addCases (fun j : Fin 1 => ?_) (fun j : Fin (width t) => ?_) i
  · simp only [equations,Fin.addCases_left,degree_sub,syntaxDegree_rename]
    have h := rootExpression_degree t
    change max 1 (syntaxDegree (rootExpression t))≤2
    omega
  · simpa only [equations,Fin.addCases_right,syntaxDegree_rename] using residual_degree t j

def system (t : Tree) : System (program t) := System.ofRows (1+width t) (equations t) (equations_degree t)

theorem holds_iff (t : Tree) (x : Fin (1+width t) → Nat) :
    (system t).Holds x ↔ x 0=rootValue t (tail t x) ∧ Valid t (tail t x) := by
  simp only [System.Holds,system,System.ofRows,Fin.forall_fin_add,equations,
    Fin.addCases_left,Fin.addCases_right,Expr.eval_sub,Expr.eval_var,Expr.eval_rename,
    natAssignment,Sum.elim_inl,Function.comp_def]
  change ((∀ _ : Fin 1,(x 0:ℤ)-(rootExpression t).eval (fun i => (tail t x i:ℤ))=0) ∧
    Valid t (tail t x)) ↔ _
  rw [rootExpression_eval]
  simp only [sub_eq_zero,Int.natCast_inj,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]

theorem holds_split (t : Tree) (v : Fin 1 → Nat) (w : Fin (width t) → Nat) :
    (system t).Holds (Fin.addCases v w) ↔ v 0=rootValue t w ∧ Valid t w := by
  rw [holds_iff]
  have ht : tail t (Fin.addCases v w)=w := by
    funext i
    simp only [tail,Fin.addCases_right]
  rw [ht]
  rfl

def representation (t : Tree) : Rep (Fin 1) (fun v => v 0=t.quote) :=
  (System.scopedRep (a:=1) (k:=width t) (system t)).ofIff (by
    intro v
    change (∃ w : Fin (width t) → Nat,(system t).Holds (Fin.addCases v w)) ↔ _
    simp only [holds_split]
    constructor
    · rintro ⟨w,ho,hw⟩
      exact ho.trans (rootValue_sound t w hw)
    · intro ho
      obtain ⟨w,hw⟩ := valid_exists t
      exact ⟨w,ho.trans (rootValue_sound t w hw).symm,hw⟩)

def graph (t : Tree) : GraphRep (fun _ : Empty → Nat => t.quote) :=
  ((representation t).reindex (fun _ : Fin 1 => (none : Option Empty))).ofIff (fun _ => Iff.rfl)

@[simp] theorem graph_witnessCount (t : Tree) : (graph t).witnessCount=4*forkCount t := by
  change width t=4*forkCount t
  exact width_eq t

theorem graph_degree (t : Tree) : (graph t).expression.toPolynomial.totalDegree≤4 := by
  simp only [graph,representation,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a:=1) (k:=width t) (system t))

theorem system_rowCount (t : Tree) : (system t).rowCount=4*forkCount t+1 := by
  change 1+width t=4*forkCount t+1
  rw [width_eq]
  omega

def formulaGraph (f : SetTheory.Form) : GraphRep (fun _ : Empty → Nat => formCode f) :=
  graph (quoteForm f)

theorem formulaGraph_witnessCount (f : SetTheory.Form) :
    (formulaGraph f).witnessCount=4*forkCount (quoteForm f) := graph_witnessCount _

theorem formulaGraph_degree (f : SetTheory.Form) :
    (formulaGraph f).expression.toPolynomial.totalDegree≤4 := graph_degree _

/-- This proof evaluates only the small count recurrence, not closed graph
syntax or a quoted formula-code numeral. -/
theorem fixedBodies_graph_counts :
    AnnotatedSyntaxGraphs.fixedBodies.map (fun f => (formulaGraph f).witnessCount)=
      [84,84,108,104,108,188,264] := by
  simp only [AnnotatedSyntaxGraphs.fixedBodies,List.map_cons,List.map_nil,formulaGraph_witnessCount]
  decide

end DiophantineConsistency.AnnotatedSharedSyntax
