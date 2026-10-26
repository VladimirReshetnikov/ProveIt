import BoundedZFCConsistency.Choice
import FirstOrder.Completeness

/-!
# Explicit sealed-ZFC proof certificates

All source data are finite unindexed syntax. Axiom instances carry their
schema arguments, and proof lines reference earlier judgments by backward
indices. No theory-membership oracle or machine/calculus translation enters
the checker.
-/

namespace DiophantineConsistency.AnnotatedProofChecker

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency

set_option maxRecDepth 12000
set_option maxHeartbeats 600000

inductive AxiomTag where
  | ext | reg | powerset | pair | union | infinity
  | separation (phi : Form)
  | replacement (psi : Form)
  | choice
  deriving DecidableEq, Repr

def AxiomTag.form : AxiomTag → Form
  | .ext => sealF Ext_form
  | .reg => sealF Reg_form
  | .powerset => sealF Pow_form
  | .pair => sealF Pair_form
  | .union => sealF Union_form
  | .infinity => sealF Inf_form
  | .separation phi => sealF (Sep_form phi)
  | .replacement psi => sealF (Repl_form psi)
  | .choice => sealF Choice_form

theorem AxiomTag.sound (tag : AxiomTag) : ZFCax_s tag.form := by
  cases tag with
  | ext => exact Or.inl (Or.inl rfl)
  | reg => exact Or.inl (Or.inr (Or.inl rfl))
  | powerset => exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  | pair => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | union => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | infinity => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | separation phi => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi,rfl⟩)))))))
  | replacement psi => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨psi,rfl⟩))))))))
  | choice => exact Or.inr rfl

theorem axiomTag_exists {f : Form} (h : ZFCax_s f) : ∃ tag : AxiomTag,tag.form=f := by
  rcases h with h | h
  · rcases h with h | h | h | h | h | h | ⟨phi,h⟩ | ⟨psi,h⟩
    · exact ⟨.ext,h.symm⟩
    · exact ⟨.reg,h.symm⟩
    · exact ⟨.powerset,h.symm⟩
    · exact ⟨.pair,h.symm⟩
    · exact ⟨.union,h.symm⟩
    · exact ⟨.infinity,h.symm⟩
    · exact ⟨.separation phi,h.symm⟩
    · exact ⟨.replacement psi,h.symm⟩
  · exact ⟨.choice,h.symm⟩

theorem axiomTags_exists (G : List Form) (hG : ∀ f ∈ G,ZFCax_s f) :
    ∃ tags : List AxiomTag,tags.map AxiomTag.form=G := by
  induction G with
  | nil => exact ⟨[],rfl⟩
  | cons f G ih =>
    obtain ⟨t,ht⟩ := axiomTag_exists (hG f (by simp))
    obtain ⟨ts,hts⟩ := ih (fun g hg => hG g (by simp [hg]))
    exact ⟨t::ts,by simp [ht,hts]⟩

structure Judgment where
  context : List Form
  conclusion : Form
  deriving DecidableEq, Repr

def Judgment.Provable (j : Judgment) : Prop := Prov j.context j.conclusion

/-- Formula/context annotations are raw data, not proof-indexed constructors. -/
inductive Rule where
  | ass (G : List Form) (a : Form)
  | impI (G : List Form) (a b : Form)
  | impE (G : List Form) (a b : Form)
  | botE (G : List Form) (a : Form)
  | lem (G : List Form) (a : Form)
  | andI (G : List Form) (a b : Form)
  | andE1 (G : List Form) (a b : Form)
  | andE2 (G : List Form) (a b : Form)
  | orI1 (G : List Form) (a b : Form)
  | orI2 (G : List Form) (a b : Form)
  | orE (G : List Form) (a b c : Form)
  | allI (G : List Form) (a : Form)
  | allE (G : List Form) (a : Form) (k : Nat)
  | exI (G : List Form) (a : Form) (k : Nat)
  | exE (G : List Form) (a c : Form)
  | eqRefl (G : List Form) (k : Nat)
  | eqElim (G : List Form) (i j : Nat) (a : Form)
  deriving DecidableEq, Repr

def Rule.output : Rule → Judgment
  | .ass G a => ⟨G,a⟩
  | .impI G a b => ⟨G,fImp a b⟩
  | .impE G _ b => ⟨G,b⟩
  | .botE G a => ⟨G,a⟩
  | .lem G a => ⟨G,fOr a (fImp a fBot)⟩
  | .andI G a b => ⟨G,fAnd a b⟩
  | .andE1 G a _ => ⟨G,a⟩
  | .andE2 G _ b => ⟨G,b⟩
  | .orI1 G a b | .orI2 G a b => ⟨G,fOr a b⟩
  | .orE G _ _ c => ⟨G,c⟩
  | .allI G a => ⟨G,fAll a⟩
  | .allE G a k => ⟨G,rename (inst k) a⟩
  | .exI G a _ => ⟨G,fEx a⟩
  | .exE G _ c => ⟨G,c⟩
  | .eqRefl G k => ⟨G,fEq k k⟩
  | .eqElim G _ j a => ⟨G,rename (inst j) a⟩

def Rule.premises : Rule → List Judgment
  | .ass _ _ | .lem _ _ | .eqRefl _ _ => []
  | .impI G a b => [⟨a::G,b⟩]
  | .impE G a b => [⟨G,fImp a b⟩,⟨G,a⟩]
  | .botE G _ => [⟨G,fBot⟩]
  | .andI G a b => [⟨G,a⟩,⟨G,b⟩]
  | .andE1 G a b | .andE2 G a b => [⟨G,fAnd a b⟩]
  | .orI1 G a _ => [⟨G,a⟩]
  | .orI2 G _ b => [⟨G,b⟩]
  | .orE G a b c => [⟨G,fOr a b⟩,⟨a::G,c⟩,⟨b::G,c⟩]
  | .allI G a => [⟨G.map (rename Nat.succ),a⟩]
  | .allE G a _ => [⟨G,fAll a⟩]
  | .exI G a k => [⟨G,rename (inst k) a⟩]
  | .exE G a c => [⟨G,fEx a⟩,⟨a::G.map (rename Nat.succ),rename Nat.succ c⟩]
  | .eqElim G i j a => [⟨G,fEq i j⟩,⟨G,rename (inst i) a⟩]

def Rule.side : Rule → Bool
  | .ass G a => decide (a∈G)
  | _ => true

theorem Rule.sound (r : Rule) (hs : r.side=true)
    (hp : ∀ j ∈ r.premises,j.Provable) : r.output.Provable := by
  cases r with
  | ass G a => exact .P_ass G a (by simpa [side] using hs)
  | impI G a b => exact .P_impI G a b (hp ⟨a::G,b⟩ (by simp [premises]))
  | impE G a b =>
    exact .P_impE G a b (hp ⟨G,fImp a b⟩ (by simp [premises])) (hp ⟨G,a⟩ (by simp [premises]))
  | botE G a => exact .P_botE G a (hp ⟨G,fBot⟩ (by simp [premises]))
  | lem G a => exact .P_lem G a
  | andI G a b =>
    exact .P_andI G a b (hp ⟨G,a⟩ (by simp [premises])) (hp ⟨G,b⟩ (by simp [premises]))
  | andE1 G a b => exact .P_andE1 G a b (hp ⟨G,fAnd a b⟩ (by simp [premises]))
  | andE2 G a b => exact .P_andE2 G a b (hp ⟨G,fAnd a b⟩ (by simp [premises]))
  | orI1 G a b => exact .P_orI1 G a b (hp ⟨G,a⟩ (by simp [premises]))
  | orI2 G a b => exact .P_orI2 G a b (hp ⟨G,b⟩ (by simp [premises]))
  | orE G a b c =>
    exact .P_orE G a b c (hp ⟨G,fOr a b⟩ (by simp [premises]))
      (hp ⟨a::G,c⟩ (by simp [premises])) (hp ⟨b::G,c⟩ (by simp [premises]))
  | allI G a => exact .P_allI G a (hp ⟨G.map (rename Nat.succ),a⟩ (by simp [premises]))
  | allE G a k => exact .P_allE G a k (hp ⟨G,fAll a⟩ (by simp [premises]))
  | exI G a k => exact .P_exI G a k (hp ⟨G,rename (inst k) a⟩ (by simp [premises]))
  | exE G a c =>
    exact .P_exE G a c (hp ⟨G,fEx a⟩ (by simp [premises]))
      (hp ⟨a::G.map (rename Nat.succ),rename Nat.succ c⟩ (by simp [premises]))
  | eqRefl G k => exact .P_eqRefl G k
  | eqElim G i j a =>
    exact .P_eqElim G i j a (hp ⟨G,fEq i j⟩ (by simp [premises]))
      (hp ⟨G,rename (inst i) a⟩ (by simp [premises]))

structure Line where
  rule : Rule
  parents : List Nat
  deriving DecidableEq, Repr

/-- Index zero is the most recently accepted line. A missing parent produces
none and cannot equal the required some judgment. -/
def Line.valid (line : Line) (seen : List Judgment) : Bool :=
  line.rule.side && decide (line.parents.map (fun i => seen[i]?)=line.rule.premises.map some)

theorem Line.sound (line : Line) (seen : List Judgment)
    (hseen : ∀ j ∈ seen,j.Provable) (h : line.valid seen=true) : line.rule.output.Provable := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
  apply line.rule.sound h.1
  intro j hj
  have hm : some j∈line.parents.map (fun i => seen[i]?) := by
    rw [h.2]
    exact List.mem_map_of_mem hj
  obtain ⟨i,_,hi⟩ := List.mem_map.mp hm
  exact hseen j (List.mem_of_getElem? hi)

/-- Failed lines abort. History stores only judgments of accepted lines. -/
def run : List Line → List Judgment → Option (List Judgment)
  | [], seen => some seen
  | line::lines, seen =>
    if line.valid seen then run lines (line.rule.output::seen) else none

theorem run_append (p q : List Line) (seen : List Judgment) :
    run (p++q) seen=(run p seen).bind (run q) := by
  induction p generalizing seen with
  | nil => rfl
  | cons line lines ih =>
    simp only [List.cons_append,run]
    split <;> simp_all

theorem run_sound (lines : List Line) (seen result : List Judgment)
    (hseen : ∀ j ∈ seen,j.Provable) (hrun : run lines seen=some result) :
    ∀ j ∈ result,j.Provable := by
  induction lines generalizing seen with
  | nil => cases hrun; exact hseen
  | cons line lines ih =>
    simp only [run] at hrun
    split at hrun
    next h =>
      apply ih _ _ hrun
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact line.sound seen hseen h
      · exact hseen j hj
    next h => contradiction

def Produces (lines : List Line) (history : List Judgment) : Prop :=
  ∀ seen,run lines seen=some (history++seen)

def HasFragment (j : Judgment) : Prop :=
  ∃ lines tail,Produces lines (j::tail)

theorem Produces.append {p q : List Line} {hp hq : List Judgment}
    (h1 : Produces p hp) (h2 : Produces q hq) : Produces (p++q) (hq++hp) := by
  intro seen
  rw [run_append,h1 seen]
  simp only [Option.bind_some]
  rw [h2 (hp++seen),List.append_assoc]

theorem Produces.step {p : List Line} {history : List Judgment} (hp : Produces p history)
    (r : Rule) (parents : List Nat)
    (hv : ∀ seen,(Line.mk r parents).valid (history++seen)=true) :
    Produces (p++[⟨r,parents⟩]) (r.output::history) := by
  intro seen
  rw [run_append,hp seen]
  simp only [Option.bind_some]
  simp only [run,hv seen,if_true,List.cons_append]

private theorem lookup_after (older : List Judgment) (j : Judgment) (tail : List Judgment) :
    (older++j::tail)[older.length]?=some j := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem fragment0 (r : Rule) (hs : r.side=true) (hm : r.premises=[]) : HasFragment r.output := by
  refine ⟨[⟨r,[]⟩],[],?_⟩
  intro seen
  simp [run,Line.valid,hs,hm]

theorem fragment1 (r : Rule) (a : Judgment) (hs : r.side=true) (hm : r.premises=[a])
    (ha : HasFragment a) : HasFragment r.output := by
  obtain ⟨p,tail,hp⟩ := ha
  refine ⟨p++[⟨r,[0]⟩],a::tail,hp.step r [0] ?_⟩
  intro seen
  simp [Line.valid,hs,hm]

theorem fragment2 (r : Rule) (a b : Judgment) (hs : r.side=true) (hm : r.premises=[a,b])
    (ha : HasFragment a) (hb : HasFragment b) : HasFragment r.output := by
  obtain ⟨p,tp,hp⟩ := ha
  obtain ⟨q,tq,hq⟩ := hb
  let history := (b::tq)++(a::tp)
  refine ⟨(p++q)++[⟨r,[(b::tq).length,0]⟩],history,?_⟩
  apply (hp.append hq).step
  intro seen
  have hfirst : (history++seen)[(b::tq).length]?=some a := by
    simpa only [history,List.append_assoc,List.cons_append] using lookup_after (b::tq) a (tp++seen)
  have hsecond : (history++seen)[0]?=some b := rfl
  simp only [Line.valid,hs,Bool.true_and,hm,List.map_cons,List.map_nil,decide_eq_true_eq]
  change [(history++seen)[(b::tq).length]?,(history++seen)[0]?]=[some a,some b]
  rw [hfirst,hsecond]

theorem fragment3 (r : Rule) (a b c : Judgment) (hs : r.side=true) (hm : r.premises=[a,b,c])
    (ha : HasFragment a) (hb : HasFragment b) (hc : HasFragment c) : HasFragment r.output := by
  obtain ⟨p,tp,hp⟩ := ha
  obtain ⟨q,tq,hq⟩ := hb
  obtain ⟨t,tt,ht⟩ := hc
  let history := (c::tt)++((b::tq)++(a::tp))
  let parents := [(c::tt).length+(b::tq).length,(c::tt).length,0]
  refine ⟨((p++q)++t)++[⟨r,parents⟩],history,?_⟩
  apply ((hp.append hq).append ht).step
  intro seen
  have hfirst : (history++seen)[(c::tt).length+(b::tq).length]?=some a := by
    have h := lookup_after ((c::tt)++(b::tq)) a (tp++seen)
    simp only [List.length_append] at h
    simpa only [history,List.append_assoc,List.cons_append] using h
  have hsecond : (history++seen)[(c::tt).length]?=some b := by
    simpa only [history,List.append_assoc,List.cons_append] using
      lookup_after (c::tt) b (tq++((a::tp)++seen))
  have hthird : (history++seen)[0]?=some c := rfl
  simp only [Line.valid,parents,hs,Bool.true_and,hm,List.map_cons,List.map_nil,decide_eq_true_eq]
  change [(history++seen)[(c::tt).length+(b::tq).length]?,
    (history++seen)[(c::tt).length]?,(history++seen)[0]?]=[some a,some b,some c]
  rw [hfirst,hsecond,hthird]

theorem fragment_exists {G : List Form} {a : Form} (h : Prov G a) : HasFragment ⟨G,a⟩ := by
  induction h with
  | P_ass G a hin => exact fragment0 (.ass G a) (by simp [Rule.side,hin]) rfl
  | P_impI G a b _ ih => exact fragment1 (.impI G a b) _ rfl rfl ih
  | P_impE G a b _ _ ih1 ih2 => exact fragment2 (.impE G a b) _ _ rfl rfl ih1 ih2
  | P_botE G a _ ih => exact fragment1 (.botE G a) _ rfl rfl ih
  | P_lem G a => exact fragment0 (.lem G a) rfl rfl
  | P_andI G a b _ _ ih1 ih2 => exact fragment2 (.andI G a b) _ _ rfl rfl ih1 ih2
  | P_andE1 G a b _ ih => exact fragment1 (.andE1 G a b) _ rfl rfl ih
  | P_andE2 G a b _ ih => exact fragment1 (.andE2 G a b) _ rfl rfl ih
  | P_orI1 G a b _ ih => exact fragment1 (.orI1 G a b) _ rfl rfl ih
  | P_orI2 G a b _ ih => exact fragment1 (.orI2 G a b) _ rfl rfl ih
  | P_orE G a b c _ _ _ ih1 ih2 ih3 => exact fragment3 (.orE G a b c) _ _ _ rfl rfl ih1 ih2 ih3
  | P_allI G a _ ih => exact fragment1 (.allI G a) _ rfl rfl ih
  | P_allE G a k _ ih => exact fragment1 (.allE G a k) _ rfl rfl ih
  | P_exI G a k _ ih => exact fragment1 (.exI G a k) _ rfl rfl ih
  | P_exE G a c _ _ ih1 ih2 => exact fragment2 (.exE G a c) _ _ rfl rfl ih1 ih2
  | P_eqRefl G k => exact fragment0 (.eqRefl G k) rfl rfl
  | P_eqElim G i j a _ _ ih1 ih2 => exact fragment2 (.eqElim G i j a) _ _ rfl rfl ih1 ih2

/-- A finite, unindexed certificate. Its data contains no axiom-membership proofs. -/
structure Certificate where
  axioms : List AxiomTag
  lines : List Line
  deriving DecidableEq, Repr

/-- Only the latest accepted line is returned. An empty certificate has no result. -/
def Certificate.result (c : Certificate) : Option Judgment :=
  (run c.lines []).bind List.head?

/-- Check a certificate against its tagged axiom context and an explicit goal. -/
def Certificate.check (c : Certificate) (goal : Form) : Bool :=
  decide (c.result=some ⟨c.axioms.map AxiomTag.form,goal⟩)

theorem Certificate.check_sound (c : Certificate) (goal : Form)
    (h : c.check goal=true) : BProv ZFCax_s [] goal := by
  simp only [check,decide_eq_true_eq,result] at h
  cases hr : run c.lines [] with
  | none => simp [hr] at h
  | some seen =>
    simp only [hr,Option.bind_some] at h
    cases seen with
    | nil => contradiction
    | cons j tail =>
      have hj : j=⟨c.axioms.map AxiomTag.form,goal⟩ := Option.some.inj h
      have hp := run_sound c.lines [] (j::tail) (by simp) hr j List.mem_cons_self
      rw [hj] at hp
      refine ⟨c.axioms.map AxiomTag.form,?_,?_⟩
      · intro f hf
        obtain ⟨tag,_,rfl⟩ := List.mem_map.mp hf
        exact tag.sound
      · simpa only [List.append_nil,Judgment.Provable] using hp

theorem certificate_exists {goal : Form} (h : BProv ZFCax_s [] goal) :
    ∃ c : Certificate,c.check goal=true := by
  obtain ⟨G,hG,hP⟩ := h
  simp only [List.append_nil] at hP
  obtain ⟨tags,ht⟩ := axiomTags_exists G hG
  obtain ⟨lines,tail,hRun⟩ := fragment_exists hP
  refine ⟨⟨tags,lines⟩,?_⟩
  have hr : run lines []=some (⟨G,goal⟩::tail) := by
    simpa only [List.append_nil] using hRun []
  simp only [Certificate.check,Certificate.result,hr,Option.bind_some,List.head?_cons,ht,
    decide_true]

/-- Exact correspondence with the original sealed-ZFC calculus, for every goal. -/
theorem exists_checked_iff (goal : Form) :
    (∃ c : Certificate,c.check goal=true) ↔ BProv ZFCax_s [] goal :=
  ⟨fun ⟨c,h⟩ => c.check_sound goal h,certificate_exists⟩

/-- A refutation certificate is accepted exactly when sealed ZFC derives bottom. -/
theorem exists_refutation_iff :
    (∃ c : Certificate,c.check fBot=true) ↔ BProv ZFCax_s [] fBot :=
  exists_checked_iff fBot

/-- No accepted finite refutation is the syntactic consistency statement itself. -/
theorem no_refutation_iff :
    (∀ c : Certificate,c.check fBot=false) ↔ ¬ BProv ZFCax_s [] fBot := by
  rw [← exists_refutation_iff]
  simp

end DiophantineConsistency.AnnotatedProofChecker
