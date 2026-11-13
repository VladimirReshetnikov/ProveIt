from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-run-majorant-client-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-run-majorant-client-draft/PellRunMajorantClient.lean.src').read_text()
H=Path('research/ordinary13-pell-period-history-majorant-draft/PellHistoryMajorant.lean.src').read_text()
R=Path('research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src').read_text()
T=Path('Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean').read_text()
S=Path('Lean/DiophantineConsistency/PRAWitnessPR.lean').read_text()
Q=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for s in ['def pairValueBound : BoundTerm 3','exp2 (poly ‘2 * (#2 + 2) * #1’) (poly ‘0’)',
 'let S : BoundTerm 3 := add (add F F) (poly ‘1’)', 'mul S S',
 'def PellValueMajorant : Prop','(e : Fin 3 → V) (i : V)',
 'i ≤ e 1 →','fun j : Fin 1 => e j.succ.succ']:assert s in H,s
for s in ['| poly P, e => P.val e Empty.elim','| add A B, e => A.vval e + B.vval e',
 '| mul A B, e => A.vval e * B.vval e',
 '| exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))']:assert s in T,s
for s in ['theorem pairValueBound_vval (e : Fin 3 → V)',
 '(2*Exp.exp (2*(e 2+2)*e 1)+1)*(2*Exp.exp (2*(e 2+2)*e 1)+1)',
 'theorem pellValueMajorant : PellValueMajorant',
 'funext fun j => Fin.cases rfl (fun l => l.elim0) j',
 'change run i (e 2) ≤ pairValueBound.vval e',
 'exact run_le_exponential_horizon i (e 1) (e 2) hi']:assert s in P,s
assert '(fun j : Fin 1 => e j.succ.succ) = ![e 2] := funext fun j => Fin.cases rfl (fun l => l.elim0) j' in S
assert 'noncomputable def run (time b : V) : V := construction.result ![b] time' in Q
for s in ['theorem wb_resultDef {k : ℕ} (p : PR.Blueprint k)',
 '(hz : WB M p.zero.val) (hs : WB M p.succ.val) (H : BoundTerm (k + 2))',
 'i ≤ e 1 → (c V).result (fun j => e j.succ.succ) i ≤ H.vval e',
 'WB M p.resultDef.val']:assert s in S,s
assert 'theorem run_le_exponential_horizon (i u a : V) (hi : i ≤ u)' in R
# Interpret constructors independently as functions on a concrete finite context.
def poly(e):return 2*(e[2]+2)*e[1]
def value(e):
 F=2**(poly(e)*2**0);S=F+F+1
 return S*S
for time in range(7):
 for a in range(7):
  val=value([0,time,a]);assert val==value([105,time,a])
  F=2**(2*(a+2)*time);assert val==(2*F+1)**2
  for j in range(1):assert [0,time,a][j+2]==[a][j]
assert value([0,3,1])!=value([0,1,3])
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'valuation_constructor_and_context_checked':True,'fin_one_mapping_matches_existing_proof':True,
 'majorant_is_exact_hH_shape_after_instantiation':True,'zero_and_successor_WB_open':True,
 'lean_elaboration_checked':False,'lean_executed':False},indent=2,sort_keys=True))
