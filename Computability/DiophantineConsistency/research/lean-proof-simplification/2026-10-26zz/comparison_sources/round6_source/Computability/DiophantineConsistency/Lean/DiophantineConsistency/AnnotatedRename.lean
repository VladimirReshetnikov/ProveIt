import DiophantineConsistency.AnnotatedCodeArithmetic

/-!
# Finite arithmetic computation tables for formula renaming

Rows contain only natural fields. Local conditions use exact numeric
constructor equations and backward references; no recursive formula parser is
consulted. Internal model-omega verification is a separate obligation.
-/

namespace DiophantineConsistency.AnnotatedRename

open SetTheory SetTheory.Form
open AnnotatedProofCode AnnotatedCodeArithmetic

set_option maxRecDepth 12000
set_option maxHeartbeats 600000
attribute [local irreducible] Nat.unpair

/-- Mode zero shifts free indices; a nonzero mode instantiates index zero
with `k`. `depth` counts binders crossed by this computation. -/
def index (mode k depth i : Nat) : Nat :=
  if i<depth then i else if mode=0 then i+1 else if i=depth then k+depth else i-1

theorem index_up (mode k depth : Nat) : index mode k (depth+1)=up (index mode k depth) := by
  funext i
  cases i with
  | zero => simp [index,up]
  | succ i => simp only [index,up]; split_ifs <;> omega

theorem index_shift (k : Nat) : index 0 k 0=Nat.succ := by
  funext i
  simp [index]

theorem index_inst (mode k : Nat) (hm : mode≠0) : index mode k 0=inst k := by
  funext i
  cases i <;> simp [index,inst,hm]

def renamed (mode k depth : Nat) (f : Form) : Form := rename (index mode k depth) f

@[simp] theorem renamed_all (mode k d : Nat) (f : Form) :
    renamed mode k d (fAll f)=fAll (renamed mode k (d+1) f) := by
  simp only [renamed,rename,←index_up]
@[simp] theorem renamed_ex (mode k d : Nat) (f : Form) :
    renamed mode k d (fEx f)=fEx (renamed mode k (d+1) f) := by
  simp only [renamed,rename,←index_up]

def atomCode (n : Nat) : Nat := (Tree.atom n).quote
def forkCode (a b : Nat) : Nat := Nat.pair (a+1) b+1

def variableCode (tag i j : Nat) : Nat :=
  forkCode (atomCode tag) (forkCode (atomCode i) (atomCode j))
def binaryCode (tag a b : Nat) : Nat := forkCode (atomCode tag) (forkCode a b)
def unaryCode (tag a : Nat) : Nat := forkCode (atomCode tag) a
def bottomCode : Nat := forkCode (atomCode 2) (atomCode 0)

@[simp] theorem code_mem (i j : Nat) : formCode (fMem i j)=variableCode 0 i j := rfl
@[simp] theorem code_eq (i j : Nat) : formCode (fEq i j)=variableCode 1 i j := rfl
@[simp] theorem code_bot : formCode fBot=bottomCode := rfl
@[simp] theorem code_imp (a b : Form) : formCode (fImp a b)=binaryCode 3 (formCode a) (formCode b) := rfl
@[simp] theorem code_and (a b : Form) : formCode (fAnd a b)=binaryCode 4 (formCode a) (formCode b) := rfl
@[simp] theorem code_or (a b : Form) : formCode (fOr a b)=binaryCode 5 (formCode a) (formCode b) := rfl
@[simp] theorem code_all (a : Form) : formCode (fAll a)=unaryCode 6 (formCode a) := rfl
@[simp] theorem code_ex (a : Form) : formCode (fEx a)=unaryCode 7 (formCode a) := rfl

structure Row where
  tag : Nat
  depth : Nat
  first : Nat
  second : Nat
  input : Nat
  output : Nat
  deriving DecidableEq, Repr

/-- Named local arithmetic conditions, suitable for a later internal
interpretation without decoding nonstandard codes to external Lean syntax. -/
def atomicEquations (mode k : Nat) (r : Row) : Bool :=
  decide (r.input=variableCode r.tag r.first r.second ∧
    r.output=variableCode r.tag (index mode k r.depth r.first) (index mode k r.depth r.second))
def bottomEquations (r : Row) : Bool :=
  decide (r.first=0 ∧ r.second=0 ∧ r.input=bottomCode ∧ r.output=bottomCode)
def binaryEquations (r a b : Row) : Bool :=
  decide (a.depth=r.depth ∧ b.depth=r.depth ∧
    r.input=binaryCode r.tag a.input b.input ∧ r.output=binaryCode r.tag a.output b.output)
def unaryEquations (r a : Row) : Bool :=
  decide (r.second=0 ∧ a.depth=r.depth+1 ∧
    r.input=unaryCode r.tag a.input ∧ r.output=unaryCode r.tag a.output)

def binaryAt (r : Row) (seen : List Row) : Bool :=
  match seen[r.first]?,seen[r.second]? with
  | some a,some b => binaryEquations r a b
  | _,_ => false

def unaryAt (r : Row) (seen : List Row) : Bool :=
  match seen[r.first]? with
  | some a => unaryEquations r a
  | _ => false

def Row.valid (mode k : Nat) (r : Row) (seen : List Row) : Bool :=
  if r.tag=0 then atomicEquations mode k r
  else if r.tag=1 then atomicEquations mode k r
  else if r.tag=2 then bottomEquations r
  else if r.tag=3 ∨ r.tag=4 ∨ r.tag=5 then binaryAt r seen
  else if r.tag=6 ∨ r.tag=7 then unaryAt r seen
  else false

def Row.Good (mode k : Nat) (r : Row) : Prop :=
  ∃ f : Form,r.input=formCode f ∧ r.output=formCode (renamed mode k r.depth f)

private theorem lookup_mem {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]?=some a) : a∈xs :=
  List.mem_of_getElem? h

theorem binary_sound (mode k : Nat) (r : Row) (seen : List Row)
    (hs : ∀ a∈seen,a.Good mode k) (ht : r.tag=3 ∨ r.tag=4 ∨ r.tag=5)
    (h : binaryAt r seen=true) : r.Good mode k := by
  unfold binaryAt at h
  cases ha : seen[r.first]? with
  | none => simp [ha] at h
  | some a =>
    cases hb : seen[r.second]? with
    | none => simp [ha,hb] at h
    | some b =>
      simp only [ha,hb,binaryEquations,decide_eq_true_eq] at h
      obtain ⟨f,hfi,hfo⟩ := hs a (lookup_mem ha)
      obtain ⟨g,hgi,hgo⟩ := hs b (lookup_mem hb)
      rcases h with ⟨hda,hdb,hi,ho⟩
      rcases ht with h3 | h4 | h5
      · refine ⟨fImp f g,?_,?_⟩
        · simpa only [h3,hfi,hgi,code_imp] using hi
        · simpa only [h3,hfo,hgo,hda,hdb,renamed,rename,code_imp] using ho
      · refine ⟨fAnd f g,?_,?_⟩
        · simpa only [h4,hfi,hgi,code_and] using hi
        · simpa only [h4,hfo,hgo,hda,hdb,renamed,rename,code_and] using ho
      · refine ⟨fOr f g,?_,?_⟩
        · simpa only [h5,hfi,hgi,code_or] using hi
        · simpa only [h5,hfo,hgo,hda,hdb,renamed,rename,code_or] using ho

theorem unary_sound (mode k : Nat) (r : Row) (seen : List Row)
    (hs : ∀ a∈seen,a.Good mode k) (ht : r.tag=6 ∨ r.tag=7)
    (h : unaryAt r seen=true) : r.Good mode k := by
  unfold unaryAt at h
  cases ha : seen[r.first]? with
  | none => simp [ha] at h
  | some a =>
    simp only [ha,unaryEquations,decide_eq_true_eq] at h
    obtain ⟨f,hfi,hfo⟩ := hs a (lookup_mem ha)
    rcases h with ⟨_,hd,hi,ho⟩
    rcases ht with h6 | h7
    · refine ⟨fAll f,?_,?_⟩
      · simpa only [h6,hfi,code_all] using hi
      · simpa only [h6,hfo,hd,renamed_all,code_all] using ho
    · refine ⟨fEx f,?_,?_⟩
      · simpa only [h7,hfi,code_ex] using hi
      · simpa only [h7,hfo,hd,renamed_ex,code_ex] using ho

theorem Row.sound (mode k : Nat) (r : Row) (seen : List Row)
    (hs : ∀ a∈seen,a.Good mode k) (h : r.valid mode k seen=true) : r.Good mode k := by
  unfold valid at h
  split at h
  next h0 =>
    simp only [atomicEquations,decide_eq_true_eq] at h
    refine ⟨fMem r.first r.second,?_,?_⟩
    · simpa only [h0,code_mem] using h.1
    · simpa only [h0,renamed,rename,code_mem] using h.2
  next h0 =>
    split at h
    next h1 =>
      simp only [atomicEquations,decide_eq_true_eq] at h
      refine ⟨fEq r.first r.second,?_,?_⟩
      · simpa only [h1,code_eq] using h.1
      · simpa only [h1,renamed,rename,code_eq] using h.2
    next h1 =>
      split at h
      next h2 =>
        simp only [bottomEquations,decide_eq_true_eq] at h
        exact ⟨fBot,by simpa only [code_bot] using h.2.2.1,
          by simpa only [renamed,rename,code_bot] using h.2.2.2⟩
      next h2 =>
        split at h
        next hb => exact binary_sound mode k r seen hs hb h
        next hb =>
          split at h
          next hu => exact unary_sound mode k r seen hs hu h
          next hu => contradiction

def run (mode k : Nat) : List Row → List Row → Option (List Row)
  | [],seen => some seen
  | r::rs,seen => if r.valid mode k seen then run mode k rs (r::seen) else none

theorem run_append (mode k : Nat) (p q seen : List Row) :
    run mode k (p++q) seen=(run mode k p seen).bind (run mode k q) := by
  induction p generalizing seen with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append,run]; split <;> simp_all

theorem run_sound (mode k : Nat) (rows seen result : List Row)
    (hs : ∀ a∈seen,a.Good mode k) (hr : run mode k rows seen=some result) :
    ∀ a∈result,a.Good mode k := by
  induction rows generalizing seen with
  | nil => cases hr; exact hs
  | cons r rs ih =>
    simp only [run] at hr
    split at hr
    next h =>
      apply ih _ _ hr
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Row.sound mode k a seen hs h
      · exact hs a ha
    next h => contradiction

def Produces (mode k : Nat) (rows history : List Row) : Prop :=
  ∀ seen,run mode k rows seen=some (history++seen)

theorem Produces.append {mode k : Nat} {p q hp hq : List Row}
    (h1 : Produces mode k p hp) (h2 : Produces mode k q hq) :
    Produces mode k (p++q) (hq++hp) := by
  intro seen
  rw [run_append,h1 seen]
  simp only [Option.bind_some]
  rw [h2 (hp++seen),List.append_assoc]

theorem Produces.step {mode k : Nat} {p history : List Row}
    (hp : Produces mode k p history) (r : Row)
    (hv : ∀ seen,r.valid mode k (history++seen)=true) :
    Produces mode k (p++[r]) (r::history) := by
  intro seen
  rw [run_append,hp seen]
  simp only [Option.bind_some,run,hv seen,if_true,List.cons_append]

private theorem lookup_after (older : List Row) (r : Row) (tail : List Row) :
    (older++r::tail)[older.length]?=some r := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem valid_binary (mode k : Nat) (r : Row) (seen : List Row) (a b : Row)
    (ht : r.tag=3 ∨ r.tag=4 ∨ r.tag=5) (ha : seen[r.first]?=some a)
    (hb : seen[r.second]?=some b) (he : binaryEquations r a b=true) :
    r.valid mode k seen=true := by
  rcases ht with h3 | h4 | h5
  · simpa [Row.valid,h3,binaryAt,ha,hb] using he
  · simpa [Row.valid,h4,binaryAt,ha,hb] using he
  · simpa [Row.valid,h5,binaryAt,ha,hb] using he

theorem valid_unary (mode k : Nat) (r : Row) (seen : List Row) (a : Row)
    (ht : r.tag=6 ∨ r.tag=7) (ha : seen[r.first]?=some a)
    (he : unaryEquations r a=true) : r.valid mode k seen=true := by
  rcases ht with h6 | h7
  · simpa [Row.valid,h6,unaryAt,ha] using he
  · simpa [Row.valid,h7,unaryAt,ha] using he

def Ready (mode k depth : Nat) (f : Form) : Prop :=
  ∃ rows tail r,r.depth=depth ∧ r.input=formCode f ∧
    r.output=formCode (renamed mode k depth f) ∧ Produces mode k rows (r::tail)

def binaryForm (tag : Nat) (f g : Form) : Form :=
  if tag=3 then fImp f g else if tag=4 then fAnd f g else fOr f g

def unaryForm (tag : Nat) (f : Form) : Form := if tag=6 then fAll f else fEx f

theorem ready_binary (mode k depth tag : Nat) (f g : Form)
    (ht : tag=3 ∨ tag=4 ∨ tag=5) (hf : Ready mode k depth f) (hg : Ready mode k depth g) :
    Ready mode k depth (binaryForm tag f g) := by
  obtain ⟨p,tp,a,had,hai,hao,hp⟩ := hf
  obtain ⟨q,tq,b,hbd,hbi,hbo,hq⟩ := hg
  let history := (b::tq)++(a::tp)
  let r : Row := ⟨tag,depth,(b::tq).length,0,
    binaryCode tag (formCode f) (formCode g),
    binaryCode tag (formCode (renamed mode k depth f)) (formCode (renamed mode k depth g))⟩
  refine ⟨(p++q)++[r],history,r,rfl,?_,?_,(hp.append hq).step r ?_⟩
  · rcases ht with rfl | rfl | rfl <;> simp [r,binaryForm]
  · rcases ht with rfl | rfl | rfl <;> simp [r,binaryForm,renamed,rename]
  · intro seen
    apply valid_binary mode k r (history++seen) a b
    · exact ht
    · simpa only [r,history,List.append_assoc,List.cons_append] using
        lookup_after (b::tq) a (tp++seen)
    · rfl
    · simp [binaryEquations,r,had,hbd,hai,hbi,hao,hbo]

theorem ready_unary (mode k depth tag : Nat) (f : Form)
    (ht : tag=6 ∨ tag=7) (hf : Ready mode k (depth+1) f) :
    Ready mode k depth (unaryForm tag f) := by
  obtain ⟨p,tp,a,had,hai,hao,hp⟩ := hf
  let r : Row := ⟨tag,depth,0,0,unaryCode tag (formCode f),
    unaryCode tag (formCode (renamed mode k (depth+1) f))⟩
  refine ⟨p++[r],a::tp,r,rfl,?_,?_,hp.step r ?_⟩
  · rcases ht with rfl | rfl <;> simp [r,unaryForm]
  · rcases ht with rfl | rfl <;> simp [r,unaryForm]
  · intro seen
    apply valid_unary mode k r ((a::tp)++seen) a
    · exact ht
    · rfl
    · simp [unaryEquations,r,had,hai,hao]

/-- Every actual formula has an accepted finite arithmetic renaming table.
The existential data are constructed by syntax induction, with no selection
from a computability proposition and no Prop-to-Type elimination. -/
theorem ready (mode k depth : Nat) (f : Form) : Ready mode k depth f := by
  induction f generalizing depth with
  | fMem i j =>
    let r : Row := ⟨0,depth,i,j,variableCode 0 i j,
      variableCode 0 (index mode k depth i) (index mode k depth j)⟩
    refine ⟨[r],[],r,rfl,rfl,rfl,?_⟩
    intro seen
    simp [run,Row.valid,r,atomicEquations]
  | fEq i j =>
    let r : Row := ⟨1,depth,i,j,variableCode 1 i j,
      variableCode 1 (index mode k depth i) (index mode k depth j)⟩
    refine ⟨[r],[],r,rfl,rfl,rfl,?_⟩
    intro seen
    simp [run,Row.valid,r,atomicEquations]
  | fBot =>
    let r : Row := ⟨2,depth,0,0,bottomCode,bottomCode⟩
    refine ⟨[r],[],r,rfl,rfl,rfl,?_⟩
    intro seen
    simp [run,Row.valid,r,bottomEquations]
  | fImp f g hf hg => exact ready_binary mode k depth 3 f g (by simp) (hf depth) (hg depth)
  | fAnd f g hf hg => exact ready_binary mode k depth 4 f g (by simp) (hf depth) (hg depth)
  | fOr f g hf hg => exact ready_binary mode k depth 5 f g (by simp) (hf depth) (hg depth)
  | fAll f hf => exact ready_unary mode k depth 6 f (by simp) (hf (depth+1))
  | fEx f hf => exact ready_unary mode k depth 7 f (by simp) (hf (depth+1))

def checkTable (mode k depth input output : Nat) (rows : List Row) : Bool :=
  match run mode k rows [] with
  | some (r::_) => decide (r.depth=depth ∧ r.input=input ∧ r.output=output)
  | _ => false

theorem checkTable_sound (mode k depth input output : Nat) (rows : List Row)
    (h : checkTable mode k depth input output rows=true) :
    ∃ f : Form,input=formCode f ∧ output=formCode (renamed mode k depth f) := by
  unfold checkTable at h
  cases hr : run mode k rows [] with
  | none => simp [hr] at h
  | some result =>
    cases result with
    | nil => simp [hr] at h
    | cons r tail =>
      simp only [hr,decide_eq_true_eq] at h
      obtain ⟨f,hfi,hfo⟩ := run_sound mode k rows [] (r::tail) (by simp) hr r List.mem_cons_self
      exact ⟨f,h.2.1 ▸ hfi,by simpa only [h.1,h.2.2] using hfo⟩

theorem checkTable_complete (mode k depth : Nat) (f : Form) :
    ∃ rows,checkTable mode k depth (formCode f) (formCode (renamed mode k depth f)) rows=true := by
  obtain ⟨rows,tail,r,hd,hi,ho,hr⟩ := ready mode k depth f
  refine ⟨rows,?_⟩
  have hh : run mode k rows []=some (r::tail) := by simpa only [List.append_nil] using hr []
  simp only [checkTable,hh,hd,hi,ho,and_self,decide_true]

theorem formCode_injective : Function.Injective formCode := by
  intro a b h
  have hh := congrArg parseFormCode h
  simpa only [parseFormCode_formCode,Option.some.injEq] using hh

/-- Exact arithmetic-table semantics for a supplied original formula. -/
theorem exists_table_iff (mode k depth : Nat) (f : Form) (output : Nat) :
    (∃ rows,checkTable mode k depth (formCode f) output rows=true) ↔
      output=formCode (renamed mode k depth f) := by
  constructor
  · rintro ⟨rows,h⟩
    obtain ⟨g,hg,ho⟩ := checkTable_sound mode k depth (formCode f) output rows h
    have he : f=g := formCode_injective hg
    simpa only [←he] using ho
  · intro h
    rw [h]
    exact checkTable_complete mode k depth f

end DiophantineConsistency.AnnotatedRename
