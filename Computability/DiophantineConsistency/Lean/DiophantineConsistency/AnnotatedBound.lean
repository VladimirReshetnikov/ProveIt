import DiophantineConsistency.AnnotatedClosure
import DiophantineConsistency.AnnotatedRenameScan

/-! # Finite local arithmetic tables for the actual additive formula bound -/

namespace DiophantineConsistency.AnnotatedBound

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedCodeArithmetic
open AnnotatedRename (Row rowCode decodeRow tableCode decodeTable decodeRow_rowCode
  decodeTable_tableCode length_le_tableCode formCode_injective binaryForm unaryForm)
open AnnotatedRename (atomCode forkCode variableCode binaryCode unaryCode bottomCode
  code_mem code_eq code_bot code_imp code_and code_or code_all code_ex)

set_option maxRecDepth 12000
set_option maxHeartbeats 600000
attribute [local irreducible] Nat.unpair

/-- Depth is unused: bound is additive under binary constructors and is
unchanged under both binders. Atomic indices are the literal source indices. -/
def atomicEquations (r : Row) : Bool :=
  decide (r.input=variableCode r.tag r.first r.second ∧
    r.output=(r.first+1)+(r.second+1))
def bottomEquations (r : Row) : Bool :=
  decide (r.input=bottomCode ∧ r.output=0)
def binaryEquations (r a b : Row) : Bool :=
  decide (r.input=binaryCode r.tag a.input b.input ∧ r.output=a.output+b.output)
def unaryEquations (r a : Row) : Bool :=
  decide (r.second=0 ∧ r.input=unaryCode r.tag a.input ∧ r.output=a.output)

def binaryAt (r : Row) (seen : List Row) : Bool :=
  match seen[r.first]?,seen[r.second]? with
  | some a,some b => binaryEquations r a b
  | _,_ => false

def unaryAt (r : Row) (seen : List Row) : Bool :=
  match seen[r.first]? with
  | some a => unaryEquations r a
  | _ => false

def valid (r : Row) (seen : List Row) : Bool :=
  if r.tag=0 then atomicEquations r
  else if r.tag=1 then atomicEquations r
  else if r.tag=2 then bottomEquations r
  else if r.tag=3 ∨ r.tag=4 ∨ r.tag=5 then binaryAt r seen
  else if r.tag=6 ∨ r.tag=7 then unaryAt r seen
  else false

def Good (r : Row) : Prop := ∃ f : Form,r.input=formCode f ∧ r.output=bound f

theorem binary_sound (r : Row) (seen : List Row)
    (hs : ∀ a∈seen,Good a) (ht : r.tag=3 ∨ r.tag=4 ∨ r.tag=5)
    (h : binaryAt r seen=true) : Good r := by
  unfold binaryAt at h
  cases ha : seen[r.first]? with
  | none => simp [ha] at h
  | some a =>
    cases hb : seen[r.second]? with
    | none => simp [ha,hb] at h
    | some b =>
      simp only [ha,hb,binaryEquations,decide_eq_true_eq] at h
      obtain ⟨f,hfi,hfo⟩ := hs a (List.mem_of_getElem? ha)
      obtain ⟨g,hgi,hgo⟩ := hs b (List.mem_of_getElem? hb)
      rcases h with ⟨hi,ho⟩
      rcases ht with h3 | h4 | h5
      · refine ⟨fImp f g,?_,?_⟩
        · simpa only [h3,hfi,hgi,code_imp] using hi
        · simpa only [hfo,hgo,bound] using ho
      · refine ⟨fAnd f g,?_,?_⟩
        · simpa only [h4,hfi,hgi,code_and] using hi
        · simpa only [hfo,hgo,bound] using ho
      · refine ⟨fOr f g,?_,?_⟩
        · simpa only [h5,hfi,hgi,code_or] using hi
        · simpa only [hfo,hgo,bound] using ho

theorem unary_sound (r : Row) (seen : List Row)
    (hs : ∀ a∈seen,Good a) (ht : r.tag=6 ∨ r.tag=7)
    (h : unaryAt r seen=true) : Good r := by
  unfold unaryAt at h
  cases ha : seen[r.first]? with
  | none => simp [ha] at h
  | some a =>
    simp only [ha,unaryEquations,decide_eq_true_eq] at h
    obtain ⟨f,hfi,hfo⟩ := hs a (List.mem_of_getElem? ha)
    rcases h with ⟨_,hi,ho⟩
    rcases ht with h6 | h7
    · refine ⟨fAll f,?_,?_⟩
      · simpa only [h6,hfi,code_all] using hi
      · simpa only [hfo,bound] using ho
    · refine ⟨fEx f,?_,?_⟩
      · simpa only [h7,hfi,code_ex] using hi
      · simpa only [hfo,bound] using ho

theorem row_sound (r : Row) (seen : List Row)
    (hs : ∀ a∈seen,Good a) (h : valid r seen=true) : Good r := by
  unfold valid at h
  split at h
  next h0 =>
    simp only [atomicEquations,decide_eq_true_eq] at h
    refine ⟨fMem r.first r.second,?_,?_⟩
    · simpa only [h0,code_mem] using h.1
    · simpa only [bound] using h.2
  next h0 =>
    split at h
    next h1 =>
      simp only [atomicEquations,decide_eq_true_eq] at h
      refine ⟨fEq r.first r.second,?_,?_⟩
      · simpa only [h1,code_eq] using h.1
      · simpa only [bound] using h.2
    next h1 =>
      split at h
      next h2 =>
        simp only [bottomEquations,decide_eq_true_eq] at h
        exact ⟨fBot,by simpa only [code_bot] using h.1,
          by simpa only [bound] using h.2⟩
      next h2 =>
        split at h
        next hb => exact binary_sound r seen hs hb h
        next hb =>
          split at h
          next hu => exact unary_sound r seen hs hu h
          next hu => contradiction

def run : List Row → List Row → Option (List Row)
  | [],seen => some seen
  | r::rs,seen => if valid r seen then run rs (r::seen) else none

theorem run_append (p q seen : List Row) :
    run (p++q) seen=(run p seen).bind (run q) := by
  induction p generalizing seen with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append,run]; split <;> simp_all

theorem run_sound (rows seen result : List Row)
    (hs : ∀ a∈seen,Good a) (hr : run rows seen=some result) :
    ∀ a∈result,Good a := by
  induction rows generalizing seen with
  | nil => cases hr; exact hs
  | cons r rs ih =>
    simp only [run] at hr
    split at hr
    next h =>
      apply ih _ _ hr
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact row_sound a seen hs h
      · exact hs a ha
    next h => contradiction

def Produces (rows history : List Row) : Prop :=
  ∀ seen,run rows seen=some (history++seen)

theorem Produces.append {p q hp hq : List Row}
    (h1 : Produces p hp) (h2 : Produces q hq) :
    Produces (p++q) (hq++hp) := by
  intro seen
  rw [run_append,h1 seen]
  simp only [Option.bind_some]
  rw [h2 (hp++seen),List.append_assoc]

theorem Produces.step {p history : List Row}
    (hp : Produces p history) (r : Row)
    (hv : ∀ seen,valid r (history++seen)=true) :
    Produces (p++[r]) (r::history) := by
  intro seen
  rw [run_append,hp seen]
  simp only [Option.bind_some,run,hv seen,if_true,List.cons_append]

private theorem lookup_after (older : List Row) (r : Row) (tail : List Row) :
    (older++r::tail)[older.length]?=some r := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem valid_binary (r : Row) (seen : List Row) (a b : Row)
    (ht : r.tag=3 ∨ r.tag=4 ∨ r.tag=5) (ha : seen[r.first]?=some a)
    (hb : seen[r.second]?=some b) (he : binaryEquations r a b=true) :
    valid r seen=true := by
  rcases ht with h3 | h4 | h5
  · simpa [valid,h3,binaryAt,ha,hb] using he
  · simpa [valid,h4,binaryAt,ha,hb] using he
  · simpa [valid,h5,binaryAt,ha,hb] using he

theorem valid_unary (r : Row) (seen : List Row) (a : Row)
    (ht : r.tag=6 ∨ r.tag=7) (ha : seen[r.first]?=some a)
    (he : unaryEquations r a=true) : valid r seen=true := by
  rcases ht with h6 | h7
  · simpa [valid,h6,unaryAt,ha] using he
  · simpa [valid,h7,unaryAt,ha] using he

def Ready (f : Form) : Prop :=
  ∃ rows tail r,r.input=formCode f ∧ r.output=bound f ∧ Produces rows (r::tail)

theorem ready_binary (tag : Nat) (f g : Form)
    (ht : tag=3 ∨ tag=4 ∨ tag=5) (hf : Ready f) (hg : Ready g) :
    Ready (binaryForm tag f g) := by
  obtain ⟨p,tp,a,hai,hao,hp⟩ := hf
  obtain ⟨q,tq,b,hbi,hbo,hq⟩ := hg
  let history := (b::tq)++(a::tp)
  let r : Row := ⟨tag,0,(b::tq).length,0,
    binaryCode tag (formCode f) (formCode g),bound f+bound g⟩
  refine ⟨(p++q)++[r],history,r,?_,?_,(hp.append hq).step r ?_⟩
  · rcases ht with rfl | rfl | rfl <;> simp [r,binaryForm]
  · rcases ht with rfl | rfl | rfl <;> simp [r,binaryForm,bound]
  · intro seen
    apply valid_binary r (history++seen) a b
    · exact ht
    · simpa only [r,history,List.append_assoc,List.cons_append] using
        lookup_after (b::tq) a (tp++seen)
    · rfl
    · simp [binaryEquations,r,hai,hbi,hao,hbo]

theorem ready_unary (tag : Nat) (f : Form)
    (ht : tag=6 ∨ tag=7) (hf : Ready f) : Ready (unaryForm tag f) := by
  obtain ⟨p,tp,a,hai,hao,hp⟩ := hf
  let r : Row := ⟨tag,0,0,0,unaryCode tag (formCode f),bound f⟩
  refine ⟨p++[r],a::tp,r,?_,?_,hp.step r ?_⟩
  · rcases ht with rfl | rfl <;> simp [r,unaryForm]
  · rcases ht with rfl | rfl <;> simp [r,unaryForm,bound]
  · intro seen
    apply valid_unary r ((a::tp)++seen) a
    · exact ht
    · rfl
    · simp [unaryEquations,r,hai,hao]

/-- Existence follows by syntax induction in Prop. No syntax is selected from
an existential computability proof. -/
theorem ready (f : Form) : Ready f := by
  induction f with
  | fMem i j =>
    let r : Row := ⟨0,0,i,j,variableCode 0 i j,(i+1)+(j+1)⟩
    refine ⟨[r],[],r,rfl,rfl,?_⟩
    intro seen
    simp [run,valid,r,atomicEquations]
  | fEq i j =>
    let r : Row := ⟨1,0,i,j,variableCode 1 i j,(i+1)+(j+1)⟩
    refine ⟨[r],[],r,rfl,rfl,?_⟩
    intro seen
    simp [run,valid,r,atomicEquations]
  | fBot =>
    let r : Row := ⟨2,0,0,0,bottomCode,0⟩
    refine ⟨[r],[],r,rfl,rfl,?_⟩
    intro seen
    simp [run,valid,r,bottomEquations]
  | fImp f g hf hg => exact ready_binary 3 f g (by simp) hf hg
  | fAnd f g hf hg => exact ready_binary 4 f g (by simp) hf hg
  | fOr f g hf hg => exact ready_binary 5 f g (by simp) hf hg
  | fAll f hf => exact ready_unary 6 f (by simp) hf
  | fEx f hf => exact ready_unary 7 f (by simp) hf

def checkTable (input output : Nat) (rows : List Row) : Bool :=
  match run rows [] with
  | some (r::_) => decide (r.input=input ∧ r.output=output)
  | _ => false

theorem checkTable_sound (input output : Nat) (rows : List Row)
    (h : checkTable input output rows=true) :
    ∃ f : Form,input=formCode f ∧ output=bound f := by
  unfold checkTable at h
  cases hr : run rows [] with
  | none => simp [hr] at h
  | some result =>
    cases result with
    | nil => simp [hr] at h
    | cons r tail =>
      simp only [hr,decide_eq_true_eq] at h
      obtain ⟨f,hfi,hfo⟩ := run_sound rows [] (r::tail) (by simp) hr r List.mem_cons_self
      exact ⟨f,h.1 ▸ hfi,by simpa only [h.2] using hfo⟩

theorem checkTable_complete (f : Form) :
    ∃ rows,checkTable (formCode f) (bound f) rows=true := by
  obtain ⟨rows,tail,r,hi,ho,hr⟩ := ready f
  refine ⟨rows,?_⟩
  have hh : run rows []=some (r::tail) := by simpa only [List.append_nil] using hr []
  simp only [checkTable,hh,hi,ho,and_self,decide_true]

def checkCode (input output code : Nat) : Bool :=
  match decodeTable code code with
  | some rows => checkTable input output rows
  | none => false

@[simp] theorem checkCode_tableCode (input output : Nat) (rows : List Row) :
    checkCode input output (tableCode rows)=checkTable input output rows := by
  simp only [checkCode,decodeTable_tableCode rows (tableCode rows) (length_le_tableCode rows)]

theorem checkCode_sound (input output code : Nat)
    (h : checkCode input output code=true) : ∃ f : Form,input=formCode f ∧ output=bound f := by
  unfold checkCode at h
  cases hr : decodeTable code code with
  | none => simp [hr] at h
  | some rows =>
    rw [hr] at h
    exact checkTable_sound input output rows h

theorem exists_code_iff (f : Form) (output : Nat) :
    (∃ code : Nat,checkCode (formCode f) output code=true) ↔ output=bound f := by
  constructor
  · rintro ⟨code,h⟩
    obtain ⟨g,hg,ho⟩ := checkCode_sound (formCode f) output code h
    have he : f=g := formCode_injective hg
    simpa only [←he] using ho
  · intro h
    obtain ⟨rows,hr⟩ := checkTable_complete f
    exact ⟨tableCode rows,by simpa only [h,checkCode_tableCode] using hr⟩

/-- A bound-table certificate and the literal universal-closing iterator have
exactly the original `sealF` result. This is an external-natural statement. -/
def checkSeal (input output table closingLength : Nat) : Bool :=
  checkCode input closingLength table && decide (output=AnnotatedClosure.closeCode input closingLength)

theorem exists_seal_iff (f : Form) (output : Nat) :
    (∃ table length : Nat,checkSeal (formCode f) output table length=true) ↔
      output=formCode (sealF f) := by
  simp only [checkSeal,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨table,length,ht,ho⟩
    have hl := (exists_code_iff f length).mp ⟨table,ht⟩
    simpa only [hl,AnnotatedClosure.closeCode_sealF] using ho
  · intro h
    obtain ⟨table,ht⟩ := (exists_code_iff f (bound f)).mpr rfl
    exact ⟨table,bound f,ht,by simpa only [AnnotatedClosure.closeCode_sealF] using h⟩

end DiophantineConsistency.AnnotatedBound
