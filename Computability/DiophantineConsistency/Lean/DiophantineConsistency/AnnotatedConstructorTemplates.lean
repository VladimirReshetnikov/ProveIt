import DiophantineConsistency.AnnotatedTemplateSyntax
import DiophantineConsistency.AnnotatedSchema
import DiophantineConsistency.AnnotatedContext

/-! # Literal variable-port templates for actual schema/proof constructors -/
namespace DiophantineConsistency.AnnotatedConstructorTemplates
open SetTheory SetTheory.Form
open AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedRename
open AnnotatedTemplateSyntax
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {n : Nat}

def binary (tag : Nat) (a b : Template n) : Template n := .fork (.atom tag) (.fork a b)
def unary (tag : Nat) (a : Template n) : Template n := .fork (.atom tag) a

def fixedVariable (tag i j : Nat) : Template n := binary tag (.atom i) (.atom j)
def dynamicVariable (tag : Nat) (i j : Fin n) : Template n := binary tag (.atomPort i) (.atomPort j)

def iffTemplate (a b : Template n) : Template n := binary 4 (binary 3 a b) (binary 3 b a)
def allTemplate (a : Template n) : Template n := unary 6 a
def exTemplate (a : Template n) : Template n := unary 7 a

@[simp] theorem value_binary (tag : Nat) (a b : Template n) (x : Fin n → Nat) :
    value (binary tag a b) x=binaryCode tag (value a x) (value b x) := rfl
@[simp] theorem value_unary (tag : Nat) (a : Template n) (x : Fin n → Nat) :
    value (unary tag a) x=unaryCode tag (value a x) := rfl
@[simp] theorem value_fixedVariable (tag i j : Nat) (x : Fin n → Nat) :
    value (fixedVariable tag i j) x=variableCode tag i j := rfl
@[simp] theorem value_dynamicVariable (tag : Nat) (i j : Fin n) (x : Fin n → Nat) :
    value (dynamicVariable tag i j) x=variableCode tag (x i) (x j) := rfl
@[simp] theorem value_iffTemplate (a b : Template n) (x : Fin n → Nat) :
    value (iffTemplate a b) x=AnnotatedSchema.iffCode (value a x) (value b x) := rfl
@[simp] theorem value_allTemplate (a : Template n) (x : Fin n → Nat) :
    value (allTemplate a) x=AnnotatedSchema.allCode (value a x) := rfl
@[simp] theorem value_exTemplate (a : Template n) (x : Fin n → Nat) :
    value (exTemplate a) x=AnnotatedSchema.exCode (value a x) := rfl

/-- Raw coded head and tail. This constructor does not assert their grammar. -/
def contextCons : Template 2 := .fork (.port 0) (.port 1)
def judgment : Template 2 := .fork (.port 0) (.port 1)
def membership : Template 2 := dynamicVariable 0 0 1
def equality : Template 2 := dynamicVariable 1 0 1
def reflexivity : Template 1 := dynamicVariable 1 0 0

def taggedVariable : Template 3 := .fork (.atomPort 0) (.fork (.atomPort 1) (.atomPort 2))
def taggedBinary : Template 3 := .fork (.atomPort 0) (.fork (.port 1) (.port 2))

@[simp] theorem contextCons_eq (x : Fin 2 → Nat) : value contextCons x=forkCode (x 0) (x 1) := rfl
@[simp] theorem judgment_eq (x : Fin 2 → Nat) : value judgment x=forkCode (x 0) (x 1) := rfl
@[simp] theorem membership_eq (x : Fin 2 → Nat) : value membership x=variableCode 0 (x 0) (x 1) := rfl
@[simp] theorem equality_eq (x : Fin 2 → Nat) : value equality x=variableCode 1 (x 0) (x 1) := rfl
@[simp] theorem reflexivity_eq (x : Fin 1 → Nat) : value reflexivity x=variableCode 1 (x 0) (x 0) := rfl
@[simp] theorem taggedVariable_eq (x : Fin 3 → Nat) :
    value taggedVariable x=variableCode (x 0) (x 1) (x 2) := rfl
@[simp] theorem taggedBinary_eq (x : Fin 3 → Nat) :
    value taggedBinary x=binaryCode (x 0) (x 1) (x 2) := rfl

theorem contextCons_actual (f : Form) (G : List Form) :
    value contextCons ![formCode f,AnnotatedContext.contextCode G]=AnnotatedContext.contextCode (f::G) := rfl

theorem judgment_actual (G : List Form) (f : Form) :
    value judgment ![AnnotatedContext.contextCode G,formCode f]=judgmentCode ⟨G,f⟩ := rfl

/-- These ports are the renamed codes certified separately by the existing
schema-map validators. No formula parse is assumed by the constructor graph. -/
def separation : Template 1 :=
  allTemplate (exTemplate (allTemplate (iffTemplate (fixedVariable 0 0 1)
    (binary 4 (fixedVariable 0 0 2) (.port 0)))))

def functionTemplate (a b : Template n) : Template n :=
  allTemplate (allTemplate (allTemplate (binary 3 (binary 4 a b) (fixedVariable 1 1 0))))

def imageTemplate (a : Template n) : Template n :=
  allTemplate (exTemplate (allTemplate (iffTemplate (fixedVariable 0 0 1)
    (exTemplate (binary 4 (fixedVariable 0 0 3) a)))))

def functionBody : Template 2 := functionTemplate (.port 0) (.port 1)
def imageBody : Template 1 := imageTemplate (.port 0)
def replacement : Template 3 :=
  binary 3 (functionTemplate (.port 0) (.port 1)) (imageTemplate (.port 2))

@[simp] theorem separation_eq (x : Fin 1 → Nat) :
    value separation x=AnnotatedSchema.separationBody (x 0) := rfl
@[simp] theorem functionTemplate_eq (a b : Template n) (x : Fin n → Nat) :
    value (functionTemplate a b) x=AnnotatedSchema.functionBody (value a x) (value b x) := rfl
@[simp] theorem imageTemplate_eq (a : Template n) (x : Fin n → Nat) :
    value (imageTemplate a) x=AnnotatedSchema.imageBody (value a x) := rfl
@[simp] theorem functionBody_eq (x : Fin 2 → Nat) :
    value functionBody x=AnnotatedSchema.functionBody (x 0) (x 1) := rfl
@[simp] theorem imageBody_eq (x : Fin 1 → Nat) :
    value imageBody x=AnnotatedSchema.imageBody (x 0) := rfl
@[simp] theorem replacement_eq (x : Fin 3 → Nat) :
    value replacement x=AnnotatedSchema.replacementBody (x 0) (x 1) (x 2) := rfl

/-- Exact actual schema bodies once the independent rename interface has
supplied its three codes. Sealing remains a separate checked operation. -/
theorem separation_actual (f : Form) :
    value separation ![formCode (rename rsep f)]=formCode (Sep_form f) := rfl

theorem replacement_actual (f : Form) :
    value replacement ![formCode (rename rf1 f),formCode (rename rf2 f),formCode (rename ri f)]=
      formCode (Repl_form f) := rfl

def separationGraph : GraphRep (fun x : Fin 1 → Nat => AnnotatedSchema.separationBody (x 0)) :=
  (graph separation).ofIff (fun _ => by simp only [separation_eq])
def functionGraph : GraphRep (fun x : Fin 2 → Nat => AnnotatedSchema.functionBody (x 0) (x 1)) :=
  (graph functionBody).ofIff (fun _ => by simp only [functionBody_eq])
def imageGraph : GraphRep (fun x : Fin 1 → Nat => AnnotatedSchema.imageBody (x 0)) :=
  (graph imageBody).ofIff (fun _ => by simp only [imageBody_eq])
def replacementGraph : GraphRep (fun x : Fin 3 → Nat => AnnotatedSchema.replacementBody (x 0) (x 1) (x 2)) :=
  (graph replacement).ofIff (fun _ => by simp only [replacement_eq])

theorem template_widths :
    [width contextCons,width judgment,width membership,width equality,width reflexivity,
      width taggedVariable,width taggedBinary,width separation,width functionBody,width imageBody,width replacement]=
    [4,4,10,10,10,11,9,84,36,92,136] := by decide

theorem separationGraph_witnessCount : separationGraph.witnessCount=84 := by
  change (graph separation).witnessCount=84
  rw [graph_witnessCount]
  decide

theorem functionGraph_witnessCount : functionGraph.witnessCount=36 := by
  change (graph functionBody).witnessCount=36
  rw [graph_witnessCount]
  decide

theorem imageGraph_witnessCount : imageGraph.witnessCount=92 := by
  change (graph imageBody).witnessCount=92
  rw [graph_witnessCount]
  decide

theorem replacementGraph_witnessCount : replacementGraph.witnessCount=136 := by
  change (graph replacement).witnessCount=136
  rw [graph_witnessCount]
  decide

theorem separationGraph_degree : separationGraph.expression.toPolynomial.totalDegree≤4 := graph_degree separation
theorem functionGraph_degree : functionGraph.expression.toPolynomial.totalDegree≤4 := graph_degree functionBody
theorem imageGraph_degree : imageGraph.expression.toPolynomial.totalDegree≤4 := graph_degree imageBody
theorem replacementGraph_degree : replacementGraph.expression.toPolynomial.totalDegree≤4 := graph_degree replacement

end DiophantineConsistency.AnnotatedConstructorTemplates
