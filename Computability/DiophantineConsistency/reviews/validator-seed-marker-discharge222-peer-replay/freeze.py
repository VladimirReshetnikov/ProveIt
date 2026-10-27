"""Freeze one independent clean pair; retain the complete author history by pins."""
from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
P=Path('/tmp/validator-seed-marker-discharge222-peer-od4hik4p')
O=D/'reviews/validator-seed-marker-discharge222-peer-replay'
F=D/'reviews/validator-seed-marker-discharge222-peer-replay.json'
REPORT=D/'reviews/validator-seed-marker-discharge222-peer.md'
def rec(p):
 p=Path(p);p=p if p.is_absolute()else R/p;b=p.read_bytes()
 return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
pins={};observations=0
def check(x):
 global observations
 a=rec(x['path']);assert a['sha256']==x['sha256'],(x,a)
 if 'bytes'in x:assert a['bytes']==x['bytes']
 pins[a['path']]=a;observations+=1;return a
assert not O.exists()and not F.exists()and not REPORT.exists()
assert shutil.disk_usage('/tmp').free>=512*1024**2
state=json.loads((P/'PEER.json').read_text());assert state['status']=='PASS'
inputs=json.loads((P/'INPUTS.json').read_text())
for x in inputs['pins']:check(x)
for row in state['records']:
 for key in ['source','snapshot','object','log','timing']:check(row[key])
 assert row['exit_code']==0 and row['author_object_and_full_log_equal']
assert [len(r['axiom_reports'])for r in state['records']]==[0,14]
for key in ['inputs','driver','final_authentication']:check(state[key])
author_receipt=check(rec(D/'reviews/validator-seed-marker-discharge222-author.md'))
reviewed=[]
for p in [R/'Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalRelativization.lean',
 R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedSourceBasis222.lean',
 R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorFullSeedTheory222.lean',
 Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean')]:
 reviewed.append(check(rec(p)))
O.mkdir()
for name in ['PEER.json','INPUTS.json','driver.py','final-authentication.json',
 'ValidatorSeedMarkerDischarge222.lean','ValidatorSeedMarkerDischarge222Checks.lean',
 'ValidatorSeedMarkerDischarge222.log','ValidatorSeedMarkerDischarge222.time',
 'ValidatorSeedMarkerDischarge222Checks.log','ValidatorSeedMarkerDischarge222Checks.time']:
 shutil.copyfile(P/name,O/name)
shutil.copyfile(__file__,O/'freeze.py')
save(O/'freeze-authentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Independent complete source/math review and fresh two-leaf replay of ROOT MarkerDischarge; conditional source derivation only.',
 counts=dict(cached=202,Foundation=136,artifacts=610,boundaries=45,providers=655,refresh=0),
 author_packet=inputs['packet'],author_manifest=inputs['manifest'],author_receipt=author_receipt,
 state=rec(P/'PEER.json'),durable_state=rec(O/'PEER.json'),inputs=rec(O/'INPUTS.json'),
 records=state['records'],driver=rec(O/'driver.py'),freeze=rec(O/'freeze.py'),
 final_authentication=rec(O/'final-authentication.json'),freeze_authentication=rec(O/'freeze-authentication.json'),
 reviewed_dependency_contracts=reviewed,private=str(P),provider=str(P/'lib'),
 observations=state['observations'],unique_paths=state['unique_paths'])
save(F,packet)
REPORT.write_text('''# Changing-marker discharge: independent peer review

27 October 2026. PASS, no requested correction. This reviews ROOT's entire
210-line main and 35-line Checks, the final executed author driver, cache
auditor and freeze, all eight attempt records, and the exact source
derivability/domain-set contracts used. Both final sources were fully read
again before the independent commands.

The raw membership graph fixes relation 1 and the ordered tuple(t,u).
The typed bindings retain domain(j)=(&j in #0), whereas Empty(&j) tests
(#0 in &j). Both free markers advance under shift. The actual finite-set
law splits i<j+1 into zero or successor, giving exactly
R(j+1)={free(neg domain(j))} union setShift(R(j)). The represented ALL rule
therefore leaves the unshifted R(j); weakening and cut against the actual
source tag-nonempty proof discharge the extra formula. No shift-fixed
domain theorem or variable-freshness oracle is used.

The induction predicate is k<=N -> exists j, j+k=N and Derivable R(j).
Its comparison is bounded arithmetic and Derivable has the actual Sigma1
existential proof graph; genuine IΣ1 successor induction applies. At k=N,
j=0. The exact emptyBody.free binding then permits ALL and a cut against
the source empty-object theorem, leaving only falsum. N=0 is explicit.
The result is conditional on an actual derivation of R(N), for arbitrary
internal N; it does not assert seed-theory inconsistency or construct the
missing arbitrary source-proof interpretation.

The independent provider audit checks the current complete header DAG,
202 cached modules including 136 Foundation modules, 610 custom artifacts,
45 explicit package/stdlib boundary primaries, and all 655 actual first
artifact providers. There is no prerequisite refresh. The historical
InternalRelativization source equals its successful 4.32 snapshot, and its
direct Proof.Basic source and primary object equal the selected current
ones. Its three server/private/IR companions remain explicitly absent.
Only its numeric finite domain-set resources are used here; neither its
old shift-fixed-domain interpretation nor a semantic source oracle enters
the argument. The full imported module is a reused authenticated object,
not independently rebuilt in this review.

All 65 author-manifest files and all eight historical input pairs were
reauthenticated. Historical leaf paths were checked through snapshots,
without pretending old source hashes still describe the current file.
Attempts 1–6 preserve local quotation/cast failures; attempt 7 compiled but
failed its report-count audit because an ambiguous name also printed an
unrelated declaration. Its unrecorded Checks object remains historical.
The final qualified Checks source has exactly 14 intended reports.

The independent pair passed on its first attempt in 14.204/1.937 seconds,
using pinned Lean 4.32, -M6000 -j1 -DElab.async=false and one thread. Both
inputs were snapshotted before compilation; both outputs are fresh regular
files in the private overlay. The 512MiB guard passed before each command
and after completion. The main log is empty; all 14 Checks reports use
only propext, Classical.choice and Quot.sound. Both compiled objects and
complete logs/reports are byte-identical to the author. No source, shared
object, Foundation cache or Git state was changed. The evidence packet
pins commands, timing/RSS, full logs, sources, objects and final rehashes.

I authored several lower C222 calculus, seed, environment and represented
checker prerequisites, and previously reviewed SourceBasis. I did not
author this ROOT MarkerDischarge pair, circuit's SourceBasis, Foundation's
raw derivability rules or the historical domain-set helper. Independence
here is the new composition's full mathematical/source review and fresh
two-leaf replay, not a claim of independently reimplementing its closure.
General source interpretation, quotient/WF/ZF/ZFC calibration and the
final equation/PA/HA proof-existence endpoint remain outside this result.

Evidence: [independent replay](validator-seed-marker-discharge222-peer-replay.json),
[full manifest](validator-seed-marker-discharge222-peer-replay/FILES.json).
Replay SHA256: '''+rec(F)['sha256']+'''.
Private provider: `/tmp/validator-seed-marker-discharge222-peer-od4hik4p/lib`.
''')
files=sorted(p for p in O.rglob('*')if p.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in files])
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),
 files=len(files),observations=observations,unique_paths=len(pins)),indent=2))
