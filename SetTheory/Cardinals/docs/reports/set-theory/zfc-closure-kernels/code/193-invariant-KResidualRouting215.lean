import BusyBeaver.ZFC.KDecoderSuffix215

/-!
Select the exact primitive-entry port by following the certified role graph.
This replaces an existential port selection with a computable selector.  It
retains the complete consumed word, so return/carry context is not discarded.
No source leaf or suffix execution is certified by this generic file alone.
-/
namespace SetTheory.BusyBeaver.ZFC.KResidualRouting215

open KZip KRuntimeCore KSim KSimPrefix KDecoderPrefix215
open RegisterPath SiteCoverage DecoderSourceBinding DecoderPaths K215Decoder
open DecoderCertificate

/-- Follow only internal decoder edges along the prefix before the final bit. -/
def followRoles (rs : Array Role) : Nat → List Bool → Option Nat
  | rid, [] => some rid
  | rid, b :: pre =>
      match rs[rid]? with
      | none => none
      | some r =>
          match (if b then r.one else r.zero) with
          | .primitive _ _ => none
          | .internal next _ => followRoles rs next pre

theorem followRoles_of_path {rs : Array Role} {first last : Nat} {pre : List Bool}
    (h : RolePath rs first pre last) : followRoles rs first pre = some last := by
  induction h with
  | nil rid => rfl
  | cons hat hedge ht ih =>
      simp only [followRoles, hat, hedge]
      exact ih

/-- The state at the exact role reached by the entire prefix. -/
def portState (rs : Array Role) (first : Nat) (pre : List Bool) : Option Nat := do
  let rid ← followRoles rs first pre
  let r ← rs[rid]?
  pure r.state

theorem portState_of_path {rs : Array Role} {first last : Nat} {pre : List Bool}
    {r : Role} (h : RolePath rs first pre last) (hat : rs[last]? = some r) :
    portState rs first pre = some r.state := by
  simp [portState, followRoles_of_path h, hat]

/-- Check only the residual primitive and return, from the certified port. -/
def checkLeafSuffix (M : TMN) (word : List Bool) (e : RegisterPath.Edge) : Bool :=
  match word.reverse with
  | [] => false
  | bit :: revPre =>
      match portState roles 0 revPre.reverse with
      | none => false
      | some q => checkEdgeFrom M word (leafPort revPre.reverse bit q) e

/-- On every accepted role route, the computable port is the routed port.
Neither the short suffix nor the physical state is used to merge contexts. -/
theorem checkLeafSuffix_of_routed {M : TMN} {word pre : List Bool} {bit : Bool}
    {q op arg : Nat} {e : RegisterPath.Edge}
    (split : word = pre ++ [bit])
    (routed : RoutedEntry formal sourceNodes roles 0 word q bit op arg) :
    checkLeafSuffix M word e = checkEdgeFrom M word (leafPort pre bit q) e := by
  obtain ⟨pre',rid,r,n,act,split',path,atRole,hq,_⟩ := routed
  have hrev : bit :: pre.reverse = bit :: pre'.reverse := by
    simpa using congrArg List.reverse (split.symm.trans split')
  have hpre : pre = pre' := by
    have hh := (List.cons.inj hrev).2
    simpa using congrArg List.reverse hh
  cases hpre
  have hs : portState roles 0 pre = some q := by
    simpa only [hq] using portState_of_path path atRole
  simp only [checkLeafSuffix, split, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.reverse_reverse, hs]

/-- A finite all-sites check discharges the universal routed-suffix premise. -/
theorem checkedLeafSuffixes_of_allSites
    (checked : allSites (checkLeafSuffix KTableCore.tm215) [] KSource215.t215 = true) :
    KDecoderSuffix215.CheckedLeafSuffixes := by
  intro word e leaf pre bit q op arg split he routed
  have hc := allSites_sound (checkLeafSuffix KTableCore.tm215) leaf [] checked
  simpa only [List.reverse_nil, List.nil_append,
    checkLeafSuffix_of_routed split routed] using hc

#print axioms followRoles_of_path
#print axioms checkLeafSuffix_of_routed
#print axioms checkedLeafSuffixes_of_allSites

end SetTheory.BusyBeaver.ZFC.KResidualRouting215
