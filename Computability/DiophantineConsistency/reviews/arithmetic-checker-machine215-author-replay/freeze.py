"""Freeze the two CheckerMachine215 attempts and reauthenticate all immutable evidence."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-checker-machine215-author-replay';F=D/'reviews/arithmetic-checker-machine215-replay.json';REPORT=D/'reviews/arithmetic-checker-machine215-author.md'
MARK=Path('/tmp/checker-machine215-controller-author-attempts.json');H=D/'research/c222-checker-machine215-plan-20261027'
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
pins={};observations=0
def check(x):
 global observations
 y=rec(x['path']);assert y['sha256']==x['sha256'],x['path']
 if 'bytes'in x:assert y['bytes']==x['bytes'],x['path']
 pins[y['path']]=y;observations+=1;return y
def link(p,d):
 p=Path(p);assert p.is_file()and not p.is_symlink()and not d.exists(),str(d)
 os.link(p,d);assert not d.is_symlink()and rec(p)['sha256']==rec(d)['sha256'];return rec(d)
assert shutil.disk_usage('/tmp').free>=512*1024**2
assert not O.exists()and not F.exists()and not REPORT.exists()
paths=json.loads(MARK.read_text());assert len(paths)==2
O.mkdir();attempts=[]
for number,path in enumerate(paths,1):
 p=Path(path);state=json.loads((p/'AUTHOR.json').read_text());inp=json.loads((p/'inputs.json').read_text())
 check(state['driver']);check(state['inputs']);check(inp['profile_reference']);assert 'profile'not in inp
 for x in inp['pins']:check(x)
 for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
 assert len(inp['actual_providers'])==681
 for x in inp['sources']:check(x['snapshot']);assert x['snapshot']['sha256']==x['sha256']
 for x in state['records']:
  check(x['snapshot']);check(x['log']);check(x['timing'])
  if 'object'in x:check(x['object'])
 artifacts=[]
 for src in inp['sources']:
  obj=p/'lib'/Path(*src['module'].split('.')).with_suffix('.olean')
  if obj.exists():
   assert obj.is_file()and not obj.is_symlink();artifacts.append(check(rec(obj)))
 out=O/f'attempt-{number:02}';out.mkdir();copies=[]
 for f in sorted(p.iterdir()):
  if f.is_file()and f.suffix in {'.json','.py','.lean','.log','.time'}:copies.append(link(f,out/f.name))
 for obj in artifacts:copies.append(link(obj['path'],out/Path(obj['path']).name))
 attempts.append(dict(number=number,private=str(p),state=check(rec(p/'AUTHOR.json')),status=state['status'],records=state['records'],available_leaf_artifacts=artifacts,immutable_hardlink_copies=copies))
final=attempts[-1];assert final['status']=='PASS'
p=Path(final['private']);state=json.loads((p/'AUTHOR.json').read_text());rows=state['records']
assert len(rows)==2 and[len(x['axiom_reports'])for x in rows]==[0,6]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256'];assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert [a['status']for a in attempts]==['FAILED','PASS'];assert sum(len(a['records'])for a in attempts)==4
assert[len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[54,41]
link(MARK,O/'attempts.json');link(__file__,O/'freeze.py')
root_notes=[check(rec(D/'reviews'/name))for name in ['arithmetic-checker-machine215-plan-root.md','arithmetic-checker-machine215-plan-root.json']]
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and complete self-review; independent replay pending.',counts=state['counts'],plan=rec(H/'cache-plan.json'),plan_manifest=rec(H/'FILES.json'),root_authorization=root_notes,final=final,attempts=attempts,provider=str(p/'lib'),final_sources=[x['source']for x in rows],final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'),evidence_storage='Regular hardlinks of immutable terminal metadata, inputs, logs, drivers and available leaf objects; originals retained.')
save(F,packet)
assert attempts[0]['records'][0]['object']['sha256']==rows[0]['object']['sha256']
REPORT.write_text(f'''# ArithmeticCheckerMachine215 — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the
54-line main, 41-line Checks and entire executed replay driver. The final
pair passed in {rows[0]['seconds']:.3f}/{rows[1]['seconds']:.3f} seconds. The main is silent;
all six reports use only propext, Classical.choice and Quot.sound. Independent
ROOT review/replay is pending. No accepted source, shared object or Git state changed.

## Exact proof-existence endpoint

The only imports are accepted ArithmeticEnumSoundnessPerm222 and ArithmeticRuntime215.
The first model-level equivalence composes actual History222.checkDef(code,1)
refutation existence with actual first-projection halting of the literal decimal215
blank machine. Both witnesses are arbitrary internal elements of the same IΣ1
model. The Type0 restriction is explicit, matching the accepted forward compiler.
No source-ZFC calibration, site correctness, desired equivalence or clock premise
is added.

haltingSentence_iff realizes the existing fixed MachineRun215.haltingSentence
in arbitrary IΣ1 models and arbitrary universes through its actual represented
run and first graphs. It does not use the standard-Nat correctness adapter.
The composed checker equivalence retains Type0. The closed checkerMachineSentence
is literally the checkDef existential equivalent to that existing sentence;
it is an ArithmeticSentence, not a claimed Sigma1 formula for the whole iff.

checkerMachineSentence_true proves validity in every Type0 IΣ1 model. Applying
Arithmetic.complete.{{0}} gives the actual IΣ1 derivation-existence theorem
isigma1_proves_checker_machine; weakening gives peano_proves_checker_machine.
This is an arithmetic proof result, not merely truth in Nat or a model-level
iff supplied as an assumption. The same current fixed syntax appears in all
model realizations and proof conclusions.

Checks bind the exact sentence by reflexivity, the arbitrary-model literal
halting graph, both internal witness directions, Type0 realization and genuine
IΣ1/PA derivation types. A propositional negative equivalence is checked for the
same predicates only. It is not identified with ConZFC, and no new closed negative
sentence or HA proof is asserted. Source-ZFC interpretation and internal polynomial
witness equivalence still precede the final HA proof-existence composition.

## Exact validation and provenance

Approved plan d46e7377a473a7c15afc40da24c0aea4f9c2f24aa2bb498999d8f818a4019ec4;
eight-file manifest 0d71ec98ff869d69d8d15d21d0d851065a2235ccfc2e94c47be439fda51896cb.
The separate ROOT authorization note and audit are pinned in this packet.
Exact scope: 232 cached modules, 95 Foundation, 517 custom artifacts,
41 boundary primaries plus 123 companions and 681 first providers; zero refresh.
Only these two new leaves compile. The accepted ROOT Runtime and EnumSoundness
objects are selected explicitly, preserving every original provenance record.
All 122 overlapping modules match source and all artifacts. The older Enum
inventory's 114 unrecorded boundary companions remain explicitly qualified as
current matches against the accepted complete Runtime boundary; no historical
capture is invented. The unequal historical KZip alternative remains recorded.

The source-header DAG, complete selected pins, compiler, all first providers and
ROOT authorization were authenticated before each run and rechecked afterward.
The isolated LEAN_PATH has pinned custom symlinks and explicit package paths;
no shared project-cache fallback or prerequisite compilation occurs. Both source
snapshots precede the first compiler command. Outputs are fresh regular files.
Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false, one thread and 512MiB guards.
All executed source/Checks/driver bytes were read before each attempt.

Two attempts and four compiler invocations are preserved. The main passed on
both attempts and its two objects are byte-identical. Initial Checks failed only
because its quoted-formula reflexivity example lacked an explicit ArithmeticSentence
annotation; Lean tried to synthesize logical connectives for the Sigma1 wrapper.
Adding that annotation leaves the main, theorem statements and intended check
unchanged. The second pair passes cleanly with six exact standard-only reports.
No cap, import, mathematical scope or accepted source changed.

The final replay authenticated {state['final_observations']} observations across
{state['unique_paths']} paths. Freeze rehashed {observations} observations across
{len(pins)} paths. All input snapshots, failed diagnostics, commands, full logs,
timings and available objects are retained as immutable regular hardlinks,
with original private paths intact. Final provider: {p}/lib.

Main source: {rows[0]['source']['sha256']}.
Checks source: {rows[1]['source']['sha256']}.
Main object: {rows[0]['object']['sha256']}.
Checks object: {rows[1]['object']['sha256']}.

I also authored the two directly imported semantic equivalences and many runtime
prerequisites. This is an author receipt, not independent review of those leaves
or this new composition. It explicitly distinguishes the new closed arithmetic
proof endpoint from the still separate source-ZFC, polynomial and HA endpoints.

Evidence: [replay](arithmetic-checker-machine215-replay.json), SHA
{rec(F)['sha256']}, and [manifest](arithmetic-checker-machine215-author-replay/FILES.json).
''')
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins),final_objects=[x['object']for x in rows]),indent=2))
