from pathlib import Path
import argparse
import difflib
import hashlib
import json

parser=argparse.ArgumentParser(description='Reproduce the reviewed semantic KSim patch against the pinned ProveIt source.')
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
args=parser.parse_args()
ROOT = args.repo.resolve()
OUT = args.out.resolve()
REL = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSim.lean')
original = (ROOT / REL).read_text()
text = original

old_halt = '''theorem runHalt_sound (hNH : ∀ b, M 230 b = none) {Q : List Bool} (h : runHalt M Q = true)
    (n : Nat) {vs : List Nat} (hv : 10 ≤ vs.length) : Halts M (conc n vs (start Q)) := by
  unfold runHalt at h
  cases hx : KHomeReady.exec M none isHalt FUEL (start Q) false with
  | none => rw [hx] at h; simp at h
  | some s =>
      obtain ⟨hh, h0, _⟩ := KHomeReady.exec_sound B n (br := none) ⟨hv, trivial⟩ FUEL (start Q) false s hx
      refine ⟨_, h0, ?_⟩
      obtain ⟨q, onl, l, r⟩ := s
      simp only [isHalt, beq_iff_eq] at hh
      subst hh
      cases onl <;> simp [conc, zl, step_zc, hNH]
'''
new_halt = '''/-- The halt checker reaches the designated state; terminality is a separate
table property and is not needed by ordinary edge simulation. -/
theorem runHalt_reaches {Q : List Bool} (h : runHalt M Q = true)
    (n : Nat) {vs : List Nat} (hv : 10 ≤ vs.length) :
    ∃ T, Reach M (conc n vs (start Q)) T ∧ T.q = 230 := by
  unfold runHalt at h
  cases hx : KHomeReady.exec M none isHalt FUEL (start Q) false with
  | none => rw [hx] at h; simp at h
  | some s =>
      obtain ⟨hh, h0, _⟩ := KHomeReady.exec_sound B n (br := none) ⟨hv, trivial⟩ FUEL (start Q) false s hx
      refine ⟨_, h0, ?_⟩
      obtain ⟨q, onl, l, r⟩ := s
      simp only [isHalt, beq_iff_eq] at hh
      cases onl <;> exact hh

theorem runHalt_sound (hNH : ∀ b, M 230 b = none) {Q : List Bool} (h : runHalt M Q = true)
    (n : Nat) {vs : List Nat} (hv : 10 ≤ vs.length) : Halts M (conc n vs (start Q)) := by
  obtain ⟨T, hT, hq⟩ := runHalt_reaches B h n hv
  exact ⟨T, hT, by simp [KZip.step, hq, hNH]⟩
'''
assert old_halt in text
text = text.replace(old_halt,new_halt)

contract = '''/-! ## Semantic site contracts

These propositions contain no symbolic executor, fuel or Boolean acceptance
condition. They are the interface for shared decoder and primitive proofs.
The existing checker remains one sound producer of these contracts. -/

/-- A complete primitive outcome for every symbolic gap and valid register file.
Positive physical progress is required by the reverse halting implication. -/
def RunsTo (M : TMN) (br : Branch) (Q : List Bool) (target : SConf) : Prop :=
  ∀ (n : Nat) {vs : List Nat}, Valid br vs →
    Reach1 M (conc n vs (start Q)) (conc n vs target)

/-- Reaching the designated terminal port does not itself assume the table has
no outgoing transitions there. The endpoint supplies that hypothesis. -/
def ReachesTerminal (M : TMN) (Q : List Bool) : Prop :=
  ∀ (n : Nat) {vs : List Nat}, 10 ≤ vs.length →
    ∃ T, Reach M (conc n vs (start Q)) T ∧ T.q = 230

/-- The complete per-edge semantic specification. The guards retain exactly
the source length and register bounds used by the established simulation. -/
def EdgeContract (M : TMN) (Q : List Bool) : Edge → Prop
  | .inc r => (Q.length ≤ 48 ∧ r < 9) ∧
      RunsTo M none Q (tgtConf (incPath Q) (allOnes Q) (.plain (.inc (physOf r))))
  | .decnz r => ((Q.length ≤ 48 ∧ r < 9) ∧
      RunsTo M (some (physOf r, true)) Q
        (tgtConf (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .none))) ∧
      RunsTo M (some (physOf r, false)) Q
        (tgtConf (incPath Q) (allOnes Q) (.plain (.dec (physOf r))))
  | .brk k => Q.length ≤ 48 ∧
      RunsTo M none Q (tgtConf (breakPath k Q) (allOnes (stripPath false k Q)) (.plain .none))
  | .cont k => Q.length ≤ 48 ∧
      RunsTo M none Q (tgtConf (continuePath k Q) false (.plain .none))
  | .halt => Q.length ≤ 48 ∧ ReachesTerminal M Q
  | .node _ => False

theorem edgeContract_length {M : TMN} {Q : List Bool} {e : Edge}
    (h : EdgeContract M Q e) : Q.length ≤ 48 := by
  cases e <;> simp_all [EdgeContract]

/-- Boolean computation is only a producer of the semantic specification. -/
theorem edgeContract_of_check {M : TMN} (B : BoxLemmas M) {Q : List Bool} {e : Edge}
    (h : checkEdge M Q e = true) : EdgeContract M Q e := by
  cases e with
  | inc r =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, fun n {_} hv => runTo_sound B h.2 n hv⟩
  | decnz r =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨⟨h.1.1, fun n {_} hv => runTo_sound B h.1.2 n hv⟩,
        fun n {_} hv => runTo_sound B h.2 n hv⟩
  | brk k | cont k =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, fun n {_} hv => runTo_sound B h.2 n hv⟩
  | halt =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, fun n {_} hv => runHalt_reaches B h.2 n hv⟩
  | node k => simp [checkEdge] at h

/-- Every actual consumed source path has its complete semantic contract.
This is deliberately indexed by the whole path, preserving occurrence coverage. -/
def SemanticCovered (M : TMN) (p : Program) : Prop :=
  ∀ P, ∃ e d, walk p (p.nnodes + 1) p.root P 0 = some (e, d) ∧
    EdgeContract M (consume P d) e

theorem semanticCovered_of_covered {M : TMN} (B : BoxLemmas M) {p : Program}
    (h : Covered M p) : SemanticCovered M p := by
  intro P
  obtain ⟨e, d, hw, hc⟩ := h P
  exact ⟨e, d, hw, edgeContract_of_check B hc⟩

/-- A shared semantic proof for every source leaf combines with a purely
structural source-totality check. No per-occurrence execution is required. -/
theorem semanticCovered_of_allLeaves {M : TMN} {p : Program} {t : RMBisim.Tree}
    (ht : RMBisim.ptree p = t)
    (htotal : SiteCoverage.allSites (fun _ _ => true) [] t = true)
    (hcontracts : ∀ {Q e}, SiteCoverage.LeafAt t Q e → EdgeContract M Q e) :
    SemanticCovered M p := by
  intro P
  obtain ⟨e, d, hw⟩ := SiteCoverage.allSites_walk_total (fun _ _ => true) p t ht htotal P
  have htw : RMBisim.twalk t P 0 = some (e, d) := by
    simpa only [← ht, ← RMBisim.walk_root] using hw
  have hleaf : SiteCoverage.LeafAt t (consume P d) e := by
    simpa only [Nat.sub_zero, RMEquiv.consume_eq] using
      (SiteCoverage.twalk_leafAt t P 0 e d htw).2
  exact ⟨e, d, hw, hcontracts hleaf⟩

'''
marker = '/-- A register configuration and the dispatch configuration that represents it. -/'
assert marker in text
text=text.replace(marker,contract+marker)

start=text.index('section Sim\n')
end=text.index('\nend Sim\n',start)
sim=text[start:end]
old_stop=sim[sim.index('omit B in\n'):sim.index('\ntheorem sim_halt')]

sim=sim.replace('section Sim','section SemanticSim')
sim=sim.replace('variable {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)\ninclude B hcov',
                'variable {M : TMN} {p : Program} (hcov : SemanticCovered M p)\ninclude hcov')
sim=sim.replace('sim_step','sim_step_semantic').replace('sim_stop','sim_stop_semantic').replace('sim_halt','sim_halt_semantic').replace('halts_iff','halts_iff_semantic')
sim=sim.replace('checkEdge_length','edgeContract_length')
sim=sim.replace('simp [checkEdge] at hck','simp [EdgeContract] at hck')
sim=sim.replace('simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at hck','simp only [EdgeContract] at hck')
sim=sim.replace('have := runTo_sound B h1 n','have := h1 n').replace('have := runTo_sound B h0 n','have := h0 n')
sim=sim.replace('omit B in\n','')
sim=sim.replace('sim_step_semantic B hcov','sim_step_semantic hcov').replace('sim_halt_semantic B hcov','sim_halt_semantic hcov')
sim=sim.replace('''  simp only [checkEdge, Bool.and_eq_true] at hck
  exact runHalt_sound B hNH hck.2 _ (vregs_length _ hext)''',
'''  obtain ⟨T', hT', hq⟩ := hck.2 _ (vregs_length _ hext)
  exact ⟨T', hT', by simp [KZip.step, hq, hNH]⟩''')
assert 'runTo_sound' not in sim and 'runHalt_sound' not in sim and 'checkEdge' not in sim

wrappers='''
end SemanticSim

/-! ## Backward-compatible Boolean-checker interface -/

section Sim

variable {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
include B hcov

theorem sim_step {c c' : Configuration} {T : Conf} (hc : Rel p c T)
    (hs : step p c = some c') : ∃ T', Rel p c' T' ∧ Reach1 M T T' :=
  sim_step_semantic (semanticCovered_of_covered B hcov) hc hs

'''+old_stop+'''

theorem sim_halt (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) (hh : AtHalt p c) : Halts M T :=
  sim_halt_semantic (semanticCovered_of_covered B hcov) hNH hc hh

/-- Existing endpoint clients continue to consume the same Boolean coverage. -/
theorem halts_iff (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) : RegisterPath.Halts p c ↔ KZip.Halts M T :=
  halts_iff_semantic (semanticCovered_of_covered B hcov) hNH hc
'''
text=text[:start]+sim+wrappers+text[end:]
target=OUT/'formal/BusyBeaver/ZFC/KSim.lean'
target.parent.mkdir(parents=True,exist_ok=True)
target.write_text(text)
patch=''.join(difflib.unified_diff(original.splitlines(keepends=True),text.splitlines(keepends=True),
    fromfile='a/'+str(REL),tofile='b/'+str(REL)))
(OUT/'KSim.semantic.patch').write_text(patch)
(OUT/'source_metrics.json').write_text(json.dumps({
    'baseline_commit':'2ca3a5c16f0876d2cab842056353c03a1ed2f5f0',
    'baseline_sha256':hashlib.sha256(original.encode()).hexdigest(),
    'candidate_sha256':hashlib.sha256(text.encode()).hexdigest(),
    'baseline_lines':len(original.splitlines()),'candidate_lines':len(text.splitlines()),
    'baseline_bytes':len(original.encode()),'candidate_bytes':len(text.encode()),
    'status':'SOURCE_METRICS_ONLY; see verification/build_result.json for compiler result'
},indent=2)+'\n')
print(target)
