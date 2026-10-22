import BusyBeaver.ZFC.KDecoderPrefix215

/-!
Residual execution after the shared K215 decoder prefix.

The semantic coverage API is inherited from the semantic-coverage proposal.
The executable residual definitions and the connection to the maintained
decoder-prefix theorem are checked here. Every residual starts with progress
FALSE; a positive suffix supplies the progress used by backward simulation.
-/
namespace SetTheory.BusyBeaver.ZFC.KResidual215

open KZip KRuntimeCore KSim KDecoderPrefix215 RegisterPath
open DecoderCertificate DecoderPaths DecoderSourceBinding K215Decoder SiteCoverage

/-- A shared prefix reaches the exact symbolic input, for every gap/register file. -/
def Prefix (M : TMN) (Q : List Bool) (input : SConf) : Prop :=
  ∀ n vs, Reach M (conc n vs (start Q)) (conc n vs input)

def runFrom (M : TMN) (br : Branch) (input target : SConf) : Bool :=
  (KHomeReady.exec M br (fun s => sMatches s target) FUEL input false).isSome

def haltFrom (M : TMN) (input : SConf) : Bool :=
  (KHomeReady.exec M none isHalt FUEL input false).isSome

theorem runFrom_sound {M : TMN} (B : BoxLemmas M) {br : Branch}
    {input target : SConf} (h : runFrom M br input target = true)
    (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    Reach1 M (conc n vs input) (conc n vs target) := by
  unfold runFrom at h
  cases hx : KHomeReady.exec M br (fun s => sMatches s target) FUEL input false with
  | none => rw [hx] at h; simp at h
  | some s =>
    obtain ⟨hm, _, hp⟩ := KHomeReady.exec_sound B n hv FUEL input false s hx
    rw [← sMatches_conc n vs hm]
    exact hp rfl

theorem haltFrom_sound {M : TMN} (B : BoxLemmas M)
    (hNH : ∀ b, M 230 b = none) {input : SConf}
    (h : haltFrom M input = true) (n : Nat) {vs : List Nat}
    (hv : 10 ≤ vs.length) : Halts M (conc n vs input) := by
  unfold haltFrom at h
  cases hx : KHomeReady.exec M none isHalt FUEL input false with
  | none => rw [hx] at h; simp at h
  | some s =>
    obtain ⟨hh, h0, _⟩ := KHomeReady.exec_sound B n (br := none) ⟨hv, trivial⟩
      FUEL input false s hx
    refine ⟨_, h0, ?_⟩
    obtain ⟨q, onl, l, r⟩ := s
    simp only [isHalt, beq_iff_eq] at hh
    subst hh
    cases onl <;> simp [conc, zl, step_zc, hNH]

/-- The edge checker retains the entire original path, both decrement guards,
all register bounds, and the exact targets from the existing simulator. -/
def checkFrom (M : TMN) (Q : List Bool) (input : SConf) : RegisterPath.Edge → Bool
  | .inc r => decide (Q.length ≤ 48) && decide (r < 9) &&
      runFrom M none input (tgtConf (incPath Q) (allOnes Q) (.plain (.inc (physOf r))))
  | .decnz r => decide (Q.length ≤ 48) && decide (r < 9) &&
      runFrom M (some (physOf r, true)) input
        (tgtConf (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .none)) &&
      runFrom M (some (physOf r, false)) input
        (tgtConf (incPath Q) (allOnes Q) (.plain (.dec (physOf r))))
  | .brk k => decide (Q.length ≤ 48) &&
      runFrom M none input
        (tgtConf (breakPath k Q) (allOnes (stripPath false k Q)) (.plain .none))
  | .cont k => decide (Q.length ≤ 48) &&
      runFrom M none input (tgtConf (continuePath k Q) false (.plain .none))
  | .halt => decide (Q.length ≤ 48) && haltFrom M input
  | .node _ => false

theorem runFrom_contract {M : TMN} (B : BoxLemmas M) {Q : List Bool}
    {input target : SConf} (prefix : Prefix M Q input) {br : Branch}
    (h : runFrom M br input target = true) : RunContract M br Q target := by
  intro n vs hv
  exact (prefix n vs).trans_reach1 (runFrom_sound B h n hv)

theorem checkFrom_contract {M : TMN} (B : BoxLemmas M) {Q : List Bool}
    {input : SConf} (prefix : Prefix M Q input) {e : RegisterPath.Edge}
    (h : checkFrom M Q input e = true) : EdgeContract M Q e := by
  cases e with
  | inc r =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, runFrom_contract B prefix h.2⟩
  | decnz r =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨⟨h.1.1, runFrom_contract B prefix h.1.2⟩, runFrom_contract B prefix h.2⟩
  | brk k | cont k =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, runFrom_contract B prefix h.2⟩
  | halt =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, fun hNH n vs hv => Halts.of_reach (prefix n vs) (haltFrom_sound B hNH h.2 n hv)⟩
  | node _ => simp [checkFrom] at h

/-- Follow the certified role graph, not merely the physical control state. -/
def followRoles (rs : Array Role) : Nat → List Bool → Option Nat
  | first, [] => some first
  | first, bit :: pre => do
    let r ← rs[first]?
    match (if bit then r.one else r.zero) with
    | .internal next _ => followRoles rs next pre
    | .primitive _ _ => none

def portState (rs : Array Role) (first : Nat) (pre : List Bool) : Option Nat := do
  let last ← followRoles rs first pre
  let r ← rs[last]?
  pure r.state

theorem followRoles_of_path {rs : Array Role} {first last : Nat} {pre : List Bool}
    (h : RolePath rs first pre last) : followRoles rs first pre = some last := by
  induction h with
  | nil => rfl
  | cons hat hedge _ ih => simpa only [followRoles,hat,Option.bind_some,hedge] using ih

private theorem snoc_pre {pre pre' : List Bool} {bit : Bool}
    (h : pre ++ [bit] = pre' ++ [bit]) : pre = pre' := by
  have hr : bit :: pre.reverse = bit :: pre'.reverse := by
    simpa using congrArg List.reverse h
  exact List.reverse_inj.mp (List.cons.inj hr).2

theorem portState_of_entry {Q pre : List Bool} {bit : Bool} {q op arg : Nat}
    (split : Q = pre ++ [bit])
    (entry : RoutedEntry formal sourceNodes roles 0 Q q bit op arg) :
    portState roles 0 pre = some q := by
  obtain ⟨pre',rid,r,n,action,split',path,hat,hq,_,_,_⟩ := entry
  have hp : pre = pre' := snoc_pre (split.symm.trans split')
  subst pre'
  simp only [portState,followRoles_of_path path,Option.bind_some,hat,hq,pure]

/-- The finite checker computes the exact port and runs only the suffix.
An absent/short role path is rejected; an empty instruction word is rejected. -/
def residualTest (M : TMN) (Q : List Bool) (e : RegisterPath.Edge) : Bool :=
  match Q.reverse with
  | [] => false
  | bit :: revPre =>
    match portState roles 0 revPre.reverse with
    | none => false
    | some q => checkFrom M Q (leafPort revPre.reverse bit q) e

theorem residualTest_at_port {M : TMN} {Q pre : List Bool} {bit : Bool}
    {q op arg : Nat} (split : Q = pre ++ [bit])
    (entry : RoutedEntry formal sourceNodes roles 0 Q q bit op arg)
    (e : RegisterPath.Edge) :
    residualTest M Q e = checkFrom M Q (leafPort pre bit q) e := by
  have hp := portState_of_entry split entry
  simp only [residualTest,split,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.singleton_append,List.reverse_reverse,hp]

theorem walk_contract (B : BoxLemmas KTableCore.tm215) (P : List Bool)
    (e : RegisterPath.Edge) (d : Nat)
    (hw : walk KSource215.p215 (KSource215.p215.nnodes+1) KSource215.p215.root P 0 = some (e,d))
    (hc : residualTest KTableCore.tm215 (consume P d) e = true) :
    EdgeContract KTableCore.tm215 (consume P d) e := by
  obtain ⟨pre,bit,q,op,arg,split,_,entry,runs⟩ := walk_prefix P e d hw
  rw [residualTest_at_port split entry e] at hc
  apply checkFrom_contract B _ hc
  intro n vs
  obtain ⟨steps,_,_,hr⟩ := runs n vs
  exact ⟨steps,hr⟩

/-- All-site residual certificates imply the original physical simulation's
semantic premise. The source relation and both simulation directions are reused. -/
theorem covered_of_residual (B : BoxLemmas KTableCore.tm215)
    (hs : allSites (residualTest KTableCore.tm215) [] KSource215.t215 = true) :
    SemanticCovered KTableCore.tm215 KSource215.p215 := by
  intro P
  obtain ⟨e,d,hw⟩ := allSites_walk_total (residualTest KTableCore.tm215)
    KSource215.p215 KSource215.t215 KSource215.t215_eq hs P
  have hc := allSites_walk (residualTest KTableCore.tm215)
    KSource215.p215 KSource215.t215 KSource215.t215_eq hs P e d hw
  exact ⟨e,d,hw,walk_contract B P e d hw hc⟩

theorem allSites_of_fast {revPrefix : List Bool} {t : RMBisim.Tree}
    (h : allSites (residualTest (KBoot.fastOf KBoot215.tt215)) revPrefix t = true) :
    allSites (residualTest KTableCore.tm215) revPrefix t = true := by
  have he : KBoot.fastOf KBoot215.tt215 = KTableCore.tm215 :=
    funext fun q => funext fun b => KBoot215.fast215 q b
  rw [← he]
  exact h

#print axioms checkFrom_contract
#print axioms walk_contract
#print axioms covered_of_residual
end SetTheory.BusyBeaver.ZFC.KResidual215
