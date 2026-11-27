import DiophantineConsistency.AnnotatedSharedSyntax

/-! # Shared quadratic syntax constructors with untrusted numeric ports -/
namespace DiophantineConsistency.AnnotatedTemplateSyntax
open AnnotatedProofCode AnnotatedRename AnnotatedSyntaxGraphs
open NaturalRegisterProgram QuadraticRegisterSystem
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

/-- A code port is an arbitrary natural, not a presumed parsed formula.
An atom port is a raw variable index and receives its own quadratic value row. -/
inductive Template (n : Nat) where
  | atom (label : Nat)
  | port (index : Fin n)
  | atomPort (index : Fin n)
  | fork (left right : Template n)
  deriving DecidableEq,Repr

variable {n : Nat}

def value : Template n → (Fin n → Nat) → Nat
  | .atom label,_ => (Tree.atom label).quote
  | .port i,x => x i
  | .atomPort i,x => (Tree.atom (x i)).quote
  | .fork a b,x => forkCode (value a x) (value b x)

def forkCount : Template n → Nat
  | .atom _ | .port _ | .atomPort _ => 0
  | .fork a b => 1+forkCount a+forkCount b

def atomPortCount : Template n → Nat
  | .atom _ | .port _ => 0
  | .atomPort _ => 1
  | .fork a b => atomPortCount a+atomPortCount b

def width : Template n → Nat
  | .atom _ | .port _ => 0
  | .atomPort _ => 1
  | .fork a b => 4+width a+width b

theorem width_eq (t : Template n) : width t=atomPortCount t+4*forkCount t := by
  induction t with
  | atom label => rfl
  | port i => rfl
  | atomPort i => rfl
  | fork a b ha hb => simp only [width,atomPortCount,forkCount]; omega

def centerIndex (a b : Template n) (i : Fin 4) : Fin (width (.fork a b)) :=
  Fin.castAdd (width b) (Fin.castAdd (width a) i)
def leftIndex (a b : Template n) (i : Fin (width a)) : Fin (width (.fork a b)) :=
  Fin.castAdd (width b) (Fin.natAdd 4 i)
def rightIndex (a b : Template n) (i : Fin (width b)) : Fin (width (.fork a b)) :=
  Fin.natAdd (4+width a) i

def assemble (a b : Template n) (center : Fin 4 → Nat) (left : Fin (width a) → Nat)
    (right : Fin (width b) → Nat) : Fin (width (.fork a b)) → Nat :=
  Fin.addCases (Fin.addCases center left) right

@[simp] theorem assemble_center (a b : Template n) (center left right) (i : Fin 4) :
    assemble a b center left right (centerIndex a b i)=center i := by
  simp only [assemble,centerIndex,Fin.addCases_left]
@[simp] theorem assemble_left (a b : Template n) (center left right) (i : Fin (width a)) :
    assemble a b center left right (leftIndex a b i)=left i := by
  simp only [assemble,leftIndex,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem assemble_right (a b : Template n) (center left right) (i : Fin (width b)) :
    assemble a b center left right (rightIndex a b i)=right i := by
  simp only [assemble,rightIndex,Fin.addCases_right]

def atomIndex (i : Fin n) : Fin (width (.atomPort i)) := ⟨0,by change 0<1; decide⟩

/-- Read a port, an inline fixed atom, or a stored computed value. -/
def rootExpression : (t : Template n) → Expr (Fin n ⊕ Fin (width t))
  | .atom label => .constant (label:ℤ)*.constant (label:ℤ)+1
  | .port i => .var (.inl i)
  | .atomPort i => .var (.inr (atomIndex i))
  | .fork a b => .var (.inr (centerIndex a b 0))

def rootValue : (t : Template n) → (Fin n → Nat) → (Fin (width t) → Nat) → Nat
  | .atom label,_,_ => (Tree.atom label).quote
  | .port i,x,_ => x i
  | .atomPort i,_,w => w (atomIndex i)
  | .fork a b,_,w => w (centerIndex a b 0)

private theorem zero_pair (label : Nat) : Nat.pair 0 label=label*label := by
  cases label with
  | zero => rfl
  | succ label => simp [Nat.pair]

@[simp] theorem rootExpression_eval (t : Template n) (x : Fin n → Nat) (w : Fin (width t) → Nat) :
    (rootExpression t).eval (natAssignment x w)=(rootValue t x w:ℤ) := by
  cases t <;> simp [rootExpression,rootValue,natAssignment,Expr.eval,Tree.quote,zero_pair]

private theorem degree_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    syntaxDegree (e.rename f)=syntaxDegree e := by
  induction e <;> simp_all [Expr.rename,syntaxDegree]
@[simp] private theorem degree_add {σ : Type*} (a b : Expr σ) :
    syntaxDegree (a+b)=max (syntaxDegree a) (syntaxDegree b) := rfl
@[simp] private theorem degree_sub {σ : Type*} (a b : Expr σ) :
    syntaxDegree (a-b)=max (syntaxDegree a) (syntaxDegree b) := rfl
@[simp] private theorem degree_mul {σ : Type*} (a b : Expr σ) :
    syntaxDegree (a*b)=syntaxDegree a+syntaxDegree b := rfl
@[simp] private theorem degree_one {σ : Type*} : syntaxDegree (1 : Expr σ)=0 := rfl

theorem rootExpression_degree (t : Template n) : syntaxDegree (rootExpression t)≤1 := by
  cases t <;> simp [rootExpression,syntaxDegree]

private theorem assignment_map {a b : Nat} (x : Fin n → Nat) (w : Fin b → Nat) (f : Fin a → Fin b) :
    natAssignment x w ∘ Sum.map id f=natAssignment x (w ∘ f) := by
  funext i
  cases i <;> rfl

private theorem local_degree {σ : Type*} (out a b bit slack maximum : Expr σ)
    (ho : syntaxDegree out≤1) (ha : syntaxDegree a≤1) (hb : syntaxDegree b≤1)
    (ht : syntaxDegree bit≤1) (hs : syntaxDegree slack≤1) (hm : syntaxDegree maximum≤1)
    (i : Fin 4) : syntaxDegree (AnnotatedSharedSyntax.localResiduals out a b bit slack maximum i)≤2 := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun z => z.elim0)))) i
  all_goals
    simp only [AnnotatedSharedSyntax.localResiduals,Fin.cases_zero,Fin.cases_succ,
      degree_add,degree_sub,degree_mul,degree_one]
    omega

/-- Each computed atom and fork is constrained once; all rows share the same
input/auxiliary scope. -/
def residual : (t : Template n) → Fin (width t) → Expr (Fin n ⊕ Fin (width t))
  | .atom _ | .port _ => fun i => Fin.elim0 i
  | .atomPort i => fun _ => .var (.inr (atomIndex i))-(.var (.inl i)*.var (.inl i)+1)
  | .fork a b =>
    Fin.addCases
      (Fin.addCases
        (AnnotatedSharedSyntax.localResiduals (.var (.inr (centerIndex a b 0)))
          ((rootExpression a).rename (Sum.map id (leftIndex a b)))
          ((rootExpression b).rename (Sum.map id (rightIndex a b)))
          (.var (.inr (centerIndex a b 1))) (.var (.inr (centerIndex a b 2)))
          (.var (.inr (centerIndex a b 3))))
        (fun i => (residual a i).rename (Sum.map id (leftIndex a b))))
      (fun i => (residual b i).rename (Sum.map id (rightIndex a b)))

def Valid (t : Template n) (x : Fin n → Nat) (w : Fin (width t) → Nat) : Prop :=
  ∀ i,(residual t i).eval (natAssignment x w)=0

theorem valid_fork_iff (a b : Template n) (x : Fin n → Nat) (w : Fin (width (.fork a b)) → Nat) :
    Valid (.fork a b) x w ↔
      ForkCertificate (w (centerIndex a b 0)) (rootValue a x (w ∘ leftIndex a b))
        (rootValue b x (w ∘ rightIndex a b)) (w (centerIndex a b 1))
        (w (centerIndex a b 2)) (w (centerIndex a b 3)) ∧
      Valid a x (w ∘ leftIndex a b) ∧ Valid b x (w ∘ rightIndex a b) := by
  have hleft := assignment_map x w (leftIndex a b)
  have hright := assignment_map x w (rightIndex a b)
  simp only [Valid,width,residual,Fin.forall_fin_add,Fin.addCases_left,Fin.addCases_right,Expr.eval_rename]
  erw [hleft,hright]
  have hl : (∀ i : Fin 4,(AnnotatedSharedSyntax.localResiduals
      (.var (.inr (centerIndex a b 0)))
      ((rootExpression a).rename (Sum.map id (leftIndex a b)))
      ((rootExpression b).rename (Sum.map id (rightIndex a b)))
      (.var (.inr (centerIndex a b 1))) (.var (.inr (centerIndex a b 2)))
      (.var (.inr (centerIndex a b 3))) i).eval (natAssignment x w)=0) ↔
      ForkCertificate (w (centerIndex a b 0)) (rootValue a x (w ∘ leftIndex a b))
        (rootValue b x (w ∘ rightIndex a b)) (w (centerIndex a b 1))
        (w (centerIndex a b 2)) (w (centerIndex a b 3)) := by
    simp only [Fin.forall_fin_succ,AnnotatedSharedSyntax.localResiduals,
      Fin.cases_zero,Fin.cases_succ,Fin.forall_fin_zero,and_true,
      Expr.eval_sub,Expr.eval_mul,Expr.eval,Expr.eval_rename]
    erw [hleft,hright,rootExpression_eval,rootExpression_eval]
    rfl
  erw [hl]
  exact and_assoc

theorem rootValue_sound (t : Template n) (x : Fin n → Nat) (w : Fin (width t) → Nat)
    (h : Valid t x w) : rootValue t x w=value t x := by
  induction t with
  | atom label => rfl
  | port i => rfl
  | atomPort i =>
    have h0 := h (atomIndex i)
    change (w (atomIndex i):ℤ)-((x i:ℤ)*(x i:ℤ)+1)=0 at h0
    simp only [rootValue,value,Tree.quote,zero_pair]
    exact_mod_cast sub_eq_zero.mp h0
  | fork a b ha hb =>
    obtain ⟨hc,hleft,hright⟩ := (valid_fork_iff a b x w).mp h
    have ho := forkCertificate_sound hc
    rw [ha _ hleft,hb _ hright] at ho
    exact ho

theorem valid_exists (t : Template n) (x : Fin n → Nat) : ∃ w : Fin (width t) → Nat,Valid t x w := by
  induction t with
  | atom label => exact ⟨Fin.elim0,fun i => i.elim0⟩
  | port i => exact ⟨Fin.elim0,fun j => j.elim0⟩
  | atomPort i =>
    refine ⟨fun _ => (Tree.atom (x i)).quote,?_⟩
    intro j
    simp [residual,Expr.eval,natAssignment,Tree.quote,zero_pair]
  | fork a b ha hb =>
    obtain ⟨left,hl⟩ := ha
    obtain ⟨right,hr⟩ := hb
    obtain ⟨bit,slack,maximum,hc⟩ := forkCertificate_complete (a:=value a x) (b:=value b x) rfl
    let center : Fin 4 → Nat := ![forkCode (value a x) (value b x),bit,slack,maximum]
    refine ⟨assemble a b center left right,(valid_fork_iff a b x _).mpr ?_⟩
    have heLeft : assemble a b center left right ∘ leftIndex a b=left := by funext i; simp
    have heRight : assemble a b center left right ∘ rightIndex a b=right := by funext i; simp
    rw [heLeft,heRight]
    refine ⟨?_,hl,hr⟩
    simp only [assemble_center,rootValue_sound a x left hl,rootValue_sound b x right hr]
    exact hc

theorem residual_degree (t : Template n) (i : Fin (width t)) : syntaxDegree (residual t i)≤2 := by
  induction t with
  | atom label => exact i.elim0
  | port j => exact i.elim0
  | atomPort j => rfl
  | fork a b ha hb =>
    refine Fin.addCases (fun j : Fin (4+width a) => ?_) (fun j : Fin (width b) => ?_) i
    · refine Fin.addCases (fun k : Fin 4 => ?_) (fun k : Fin (width a) => ?_) j
      · simp only [residual,Fin.addCases_left]
        apply local_degree
        · exact Nat.le_refl 1
        · rw [degree_rename]; exact rootExpression_degree a
        · rw [degree_rename]; exact rootExpression_degree b
        · exact Nat.le_refl 1
        · exact Nat.le_refl 1
        · exact Nat.le_refl 1
      · simpa only [residual,Fin.addCases_left,Fin.addCases_right,degree_rename] using ha k
    · simpa only [residual,Fin.addCases_right,degree_rename] using hb j

/-- Source layout is claimed output, all raw ports, then all auxiliaries. -/
def program (t : Template n) : Program ((1+n)+width t) := .empty

def outputIndex (t : Template n) : Fin ((1+n)+width t) := Fin.castAdd (width t) 0
def inputIndex (t : Template n) (i : Fin n) : Fin ((1+n)+width t) :=
  Fin.castAdd (width t) (Fin.natAdd 1 i)
def auxiliaryIndex (t : Template n) (i : Fin (width t)) : Fin ((1+n)+width t) :=
  Fin.natAdd (1+n) i

def portMap (t : Template n) : Fin n ⊕ Fin (width t) → Fin ((1+n)+width t) :=
  Sum.elim (inputIndex t) (auxiliaryIndex t)

def equations (t : Template n) : Fin (1+width t) →
    Expr (Fin ((1+n)+width t) ⊕ Fin (program t).nodes.length) :=
  Fin.addCases
    (fun _ : Fin 1 => .var (.inl (outputIndex t))-
      (rootExpression t).rename (fun i => .inl (portMap t i)))
    (fun i => (residual t i).rename (fun j => .inl (portMap t j)))

theorem equations_degree (t : Template n) (i : Fin (1+width t)) : syntaxDegree (equations t i)≤2 := by
  refine Fin.addCases (fun j : Fin 1 => ?_) (fun j : Fin (width t) => ?_) i
  · simp only [equations,Fin.addCases_left,degree_sub,degree_rename]
    have h := rootExpression_degree t
    change max 1 (syntaxDegree (rootExpression t))≤2
    omega
  · simpa only [equations,Fin.addCases_right,degree_rename] using residual_degree t j

def system (t : Template n) : System (program t) :=
  System.ofRows (1+width t) (equations t) (equations_degree t)

theorem holds_split (t : Template n) (v : Fin (1+n) → Nat) (w : Fin (width t) → Nat) :
    (system t).Holds (Fin.addCases v w) ↔
      v 0=rootValue t (fun i => v (Fin.natAdd 1 i)) w ∧
        Valid t (fun i => v (Fin.natAdd 1 i)) w := by
  have hmap : natAssignment (Fin.addCases v w) ((program t).eval (Fin.addCases v w)) ∘
      (fun i => Sum.inl (portMap t i))=natAssignment (fun i => v (Fin.natAdd 1 i)) w := by
    funext i
    cases i <;> simp only [portMap,inputIndex,auxiliaryIndex,Sum.elim_inl,Sum.elim_inr,
      Function.comp_def,natAssignment,Fin.addCases_left,Fin.addCases_right]
  have hout : natAssignment (Fin.addCases v w) ((program t).eval (Fin.addCases v w))
      (.inl (outputIndex t))=(v 0:ℤ) := by
    simp only [natAssignment,outputIndex,Fin.addCases_left,Sum.elim_inl]
  simp only [System.Holds,system,System.ofRows,Fin.forall_fin_add,equations,
    Fin.addCases_left,Fin.addCases_right,Expr.eval_sub,Expr.eval_var,Expr.eval_rename,hmap,hout]
  change ((∀ _ : Fin 1,(v 0:ℤ)-(rootExpression t).eval
    (natAssignment (fun i => v (Fin.natAdd 1 i)) w)=0) ∧
      Valid t (fun i => v (Fin.natAdd 1 i)) w) ↔ _
  rw [rootExpression_eval]
  simp only [sub_eq_zero,Int.natCast_inj,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]

def representation (t : Template n) : Rep (Fin (1+n))
    (fun v => v 0=value t (fun i => v (Fin.natAdd 1 i))) :=
  (System.scopedRep (a:=1+n) (k:=width t) (system t)).ofIff (by
    intro v
    change (∃ w : Fin (width t) → Nat,(system t).Holds (Fin.addCases v w)) ↔ _
    simp only [holds_split]
    constructor
    · rintro ⟨w,ho,hw⟩
      exact ho.trans (rootValue_sound t _ w hw)
    · intro ho
      obtain ⟨w,hw⟩ := valid_exists t (fun i => v (Fin.natAdd 1 i))
      exact ⟨w,ho.trans (rootValue_sound t _ w hw).symm,hw⟩)

private def graphIndex : Fin (1+n) → Option (Fin n) :=
  Fin.addCases (fun _ : Fin 1 => none) some

def graph (t : Template n) : GraphRep (value t) :=
  ((representation t).reindex graphIndex).ofIff (by
    intro v
    have h0 : graphIndex (0 : Fin (1+n))=none := rfl
    have hs (i : Fin n) : graphIndex (Fin.natAdd 1 i)=some i := by
      simp only [graphIndex,Fin.addCases_right]
    change (v (graphIndex 0)=value t (fun i => v (graphIndex (Fin.natAdd 1 i)))) ↔ _
    simp only [h0,hs]
    rfl)

@[simp] theorem graph_witnessCount (t : Template n) :
    (graph t).witnessCount=atomPortCount t+4*forkCount t := by
  change width t=atomPortCount t+4*forkCount t
  exact width_eq t

theorem graph_degree (t : Template n) : (graph t).expression.toPolynomial.totalDegree≤4 := by
  simp only [graph,representation,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a:=1+n) (k:=width t) (system t))

theorem system_rowCount (t : Template n) :
    (system t).rowCount=atomPortCount t+4*forkCount t+1 := by
  change 1+width t=atomPortCount t+4*forkCount t+1
  rw [width_eq]
  omega

end DiophantineConsistency.AnnotatedTemplateSyntax
