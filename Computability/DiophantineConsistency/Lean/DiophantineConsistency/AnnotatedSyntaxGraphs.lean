import DiophantineConsistency.QuadraticNatPairing
import DiophantineConsistency.AnnotatedCodeGraphs
import DiophantineConsistency.AnnotatedRenameArithmetic

/-! # Direct quadratic constructor graphs without large quoted numerals

The local fork graph has three natural auxiliaries and four quadratic rows.
Fixed tree/formula graphs are built from syntax. Their count theorem traverses
syntax metadata only; no closed whole-checker graph is constructed.
-/
namespace DiophantineConsistency.AnnotatedSyntaxGraphs
open AnnotatedProofCode AnnotatedRename
open NaturalRegisterProgram QuadraticRegisterSystem
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

/-- Exact local arithmetic rows for `out=pair(a+1,b)+1`. -/
def ForkCertificate (out a b t s m : Nat) : Prop :=
  (t:ℤ)*((t:ℤ)-1)=0 ∧
  (m:ℤ)-((1-(t:ℤ))*b+(t:ℤ)*((a:ℤ)+1))=0 ∧
  (b:ℤ)+(t:ℤ)*s-((a:ℤ)+1)-(1-(t:ℤ))*((s:ℤ)+1)=0 ∧
  (out:ℤ)-1-(m:ℤ)*m-((a:ℤ)+1)-(t:ℤ)*b=0

instance (out a b t s m : Nat) : Decidable (ForkCertificate out a b t s m) := by
  unfold ForkCertificate
  infer_instance

/-- Translate by successor, where cast cancellation is unconditional. -/
theorem forkCertificate_succ (out a b t s m : Nat) :
    ForkCertificate (out+1) a b t s m ↔
      QuadraticNatPairing.Certificate out (a+1) b t s m := by
  simp only [ForkCertificate,QuadraticNatPairing.Certificate,Nat.cast_add,
    Nat.cast_one,add_sub_cancel_right]

theorem forkCertificate_iff (out a b t s m : Nat) :
    ForkCertificate out a b t s m ↔
      QuadraticNatPairing.Certificate out.pred (a+1) b t s m ∧ 0<out := by
  cases out with
  | zero =>
    simp only [Nat.lt_irrefl,and_false,iff_false]
    intro h
    have hz := h.2.2.2
    have hn := mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg b)
    have hs := mul_self_nonneg (m:ℤ)
    omega
  | succ out =>
    simpa only [Nat.pred_succ,Nat.succ_pos,and_true] using
      forkCertificate_succ out a b t s m

theorem forkCertificate_sound {out a b t s m : Nat} (h : ForkCertificate out a b t s m) :
    out=forkCode a b := by
  obtain ⟨hc,ho⟩ := (forkCertificate_iff _ _ _ _ _ _).mp h
  have he := congrArg Nat.succ (QuadraticNatPairing.certificate_sound hc)
  simpa only [Nat.succ_pred_eq_of_pos ho,forkCode,Nat.succ_eq_add_one] using he

theorem forkCertificate_complete {out a b : Nat} (h : out=forkCode a b) :
    ∃ t s m,ForkCertificate out a b t s m := by
  subst out
  obtain ⟨t,s,m,hc⟩ := QuadraticNatPairing.certificate_complete (a:=a+1) (b:=b) rfl
  exact ⟨t,s,m,(forkCertificate_succ _ a b t s m).mpr hc⟩

def program : Program 6 := .empty
private def port (i : Fin 6) : Expr (Fin 6 ⊕ Fin program.nodes.length) := .var (.inl i)

def rows : Fin 4 → Expr (Fin 6 ⊕ Fin program.nodes.length) :=
  ![port 3*(port 3-1),
    port 5-((1-port 3)*port 2+port 3*(port 1+1)),
    port 2+port 3*port 4-(port 1+1)-(1-port 3)*(port 4+1),
    port 0-1-port 5*port 5-(port 1+1)-port 3*port 2]

def system : System program := System.ofRows 4 rows (by intro i; fin_cases i <;> decide)

theorem holds_iff (x : Fin 6 → Nat) : system.Holds x ↔
    ForkCertificate (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  simp [System.Holds,system,System.ofRows,rows,port,Expr.eval,natAssignment,ForkCertificate,
    Fin.forall_fin_succ]

def representation : Rep (Fin 3) (fun v => v 0=forkCode (v 1) (v 2)) :=
  (System.scopedRep (a:=3) (k:=3) system).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 3 → Nat,ForkCertificate (v 0) (v 1) (v 2) (w 0) (w 1) (w 2)) ↔ _
    constructor
    · rintro ⟨w,hw⟩
      exact forkCertificate_sound hw
    · intro h
      obtain ⟨t,s,m,hw⟩ := forkCertificate_complete h
      exact ⟨![t,s,m],hw⟩)

private def graphIndex : Fin 3 → Option (Fin 2) :=
  Fin.cases none (Fin.cases (some 0) (fun _ => some 1))

def forkGraph : GraphRep (fun v : Fin 2 → Nat => forkCode (v 0) (v 1)) :=
  (representation.reindex graphIndex).ofIff (fun _ => Iff.rfl)

@[simp] theorem forkGraph_witnessCount : forkGraph.witnessCount=3 := rfl

theorem forkGraph_degree : forkGraph.expression.toPolynomial.totalDegree≤4 := by
  simp only [forkGraph,representation,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a:=3) (k:=3) system)

theorem forkGraph_binaryOps : forkGraph.expression.binaryOps=54 := by decide

private theorem zero_pair (n : Nat) : Nat.pair 0 n=n*n := by
  cases n with
  | zero => rfl
  | succ n => simp [Nat.pair]

/-- Only the original atom label is a coefficient. Its squared quote is
computed by the expression rather than materialized as a large numeral. -/
def atomGraph (n : Nat) : GraphRep (fun _ : Empty → Nat => (Tree.atom n).quote) :=
  (Rep.equality (.var none) ((Expr.constant (n:ℤ))*(.constant (n:ℤ))+1)).ofIff (by
    intro v
    change (v none:ℤ)=(n:ℤ)*(n:ℤ)+1 ↔ v none=Nat.pair 0 n+1
    rw [zero_pair,←Int.natCast_mul]
    omega)

@[simp] theorem atomGraph_witnessCount (n : Nat) : (atomGraph n).witnessCount=0 := rfl

def forkCount : Tree → Nat
  | .atom _ => 0
  | .fork a b => 1+forkCount a+forkCount b

/-- Syntax-directed data, with no graph for a large quoted numeral constant. -/
def treeGraph : (t : Tree) → GraphRep (fun _ : Empty → Nat => t.quote)
  | .atom n => atomGraph n
  | .fork a b => by
    let functions : Fin 2 → (Empty → Nat) → Nat := ![fun _ => a.quote,fun _ => b.quote]
    let arguments : ∀ i,GraphRep (functions i) :=
      Fin.cases (treeGraph a) (Fin.cases (treeGraph b) (fun i => Fin.elim0 i))
    exact (GraphRep.composeDirect forkGraph arguments).ofIff (fun _ => Iff.rfl)

theorem treeGraph_witnessCount (t : Tree) : (treeGraph t).witnessCount=5*forkCount t := by
  induction t with
  | atom n => rfl
  | fork a b ha hb =>
    simp only [treeGraph,Rep.ofIff,GraphRep.composeDirect_witnessCount,
      forkGraph_witnessCount,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
      Fin.sum_univ_zero,ha,hb,forkCount]
    omega

def formulaGraph (f : SetTheory.Form) : GraphRep (fun _ : Empty → Nat => formCode f) :=
  treeGraph (quoteForm f)

theorem formulaGraph_witnessCount (f : SetTheory.Form) :
    (formulaGraph f).witnessCount=5*forkCount (quoteForm f) := treeGraph_witnessCount _

def fixedBodies : List SetTheory.Form :=
  [SetTheory.Ext_form,SetTheory.Reg_form,SetTheory.Pow_form,SetTheory.Pair_form,
    SetTheory.Union_form,SetTheory.Inf_form,LeanProofs.BoundedZFCConsistency.Choice_form]

/-- Exact fixed-body graph sizes, proved through the metadata theorem without
constructing any of the seven closed formula-graph expressions. -/
theorem fixedBodies_graph_counts :
    fixedBodies.map (fun f => (formulaGraph f).witnessCount)=[105,105,135,130,135,235,330] := by
  simp only [fixedBodies,List.map_cons,List.map_nil,formulaGraph_witnessCount]
  decide

/-- The previous standalone direct fork constructor uses five more witnesses.
This local saving makes no claim about a complete checker or compiled quartic. -/
theorem forkGraph_saves_five :
    AnnotatedCodeGraphs.forkConstructor.witnessCount=forkGraph.witnessCount+5 := by
  rw [AnnotatedCodeGraphs.forkConstructor_witnessCount,forkGraph_witnessCount]

end DiophantineConsistency.AnnotatedSyntaxGraphs
