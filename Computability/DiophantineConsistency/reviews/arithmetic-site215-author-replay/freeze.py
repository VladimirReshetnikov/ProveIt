"""Freeze the two Site215 attempts using hardlinks for immutable evidence."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-site215-author-replay'
F=D/'reviews/arithmetic-site215-replay.json'
REPORT=D/'reviews/arithmetic-site215-author.md'
MARK=Path('/tmp/site215-controller-author-attempts.json')
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
 check(state['driver']);check(state['inputs']);check(inp['profile_reference'])
 assert 'profile'not in inp
 for x in inp['pins']:check(x)
 for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
 assert len(inp['actual_providers'])==622
 for x in inp['sources']:
  check(x['snapshot']);assert x['snapshot']['sha256']==x['sha256']
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
 attempts.append(dict(number=number,private=str(p),state=check(rec(p/'AUTHOR.json')),
  status=state['status'],records=state['records'],available_leaf_artifacts=artifacts,
  immutable_hardlink_copies=copies))
final=attempts[-1];assert final['status']=='PASS'
p=Path(final['private']);state=json.loads((p/'AUTHOR.json').read_text());rows=state['records']
assert len(rows)==2 and[len(x['axiom_reports'])for x in rows]==[0,19]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256']
 assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert attempts[0]['status']=='FAILED'and sum(len(a['records'])for a in attempts)==3
assert[len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[185,76]
link(MARK,O/'attempts.json');link(__file__,O/'freeze.py')
root_plan_receipt=check(rec(D/'reviews/arithmetic-site215-plan-root.md'))
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and complete self-review; independent review pending.',
 counts=state['counts'],plan=rec(D/'research/c222-site-execution215-plan-20261027/cache-plan.json'),
 plan_manifest=rec(D/'research/c222-site-execution215-plan-20261027/FILES.json'),
 root_plan_receipt=root_plan_receipt,
 final=final,attempts=attempts,provider=str(p/'lib'),final_sources=[x['source']for x in rows],
 final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],
 final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],
 reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'),
 evidence_storage='Regular hardlinks of immutable terminal evidence; originals and all bytes retained.')
save(F,packet)
REPORT.write_text('''# ArithmeticSite215 — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully reviewed
the final 185-line main and 76-line Checks, then completed a fresh capped
private replay. Independent review is pending. Only these two new Lean
leaves and their new evidence were written; no accepted source, shared
object, shared progress document or Git state was changed.

The exact imports are ArithmeticHome215 and KSites215. The former is the
accepted actual arithmetic executor; the latter supplies the complete
literal source certificate for 4,751 leaves in 105 kernel blocks. This
packet does not rerun those closed certificates or use KSim's ordinary-Nat
runTo_sound, sim_step or halts_iff as an internal premise.

## Uniform execution and exact data

All execution statements quantify over arbitrary ORing models of IΣ1.
The gap, nine register values, positive spare count and clocks are internal,
including nonstandard values. Paths, source operations and fuel 4000 remain
finite syntax. There is no positive-gap or positive-register hypothesis.

source_checked obtains every actual checkEdge result from LeafAt and the
closed all_sites theorem. It derives path length at most 48, excludes node
operations and derives both the logical and physical register bounds.
The literal nine-entry physical map is kernel checked. No source endpoint
assumes that its site checker or desired execution succeeds.

runTo_actual extracts the actual executor result and applies accepted
Home.exec_matches_actual. runHalt_actual applies Home.exec_actual and
halt_interpret. Both begin with moved=false and therefore retain a positive
execution clock, even if individual scans or normalization steps are empty.
Halt is first(configuration)=0 at sparse state 230, in either tape-facing
orientation. The full terminal payload, final write and move are retained;
scalar configuration equality to zero is not asserted.

The six LeafAt clients cover INC, DEC zero, DEC positive, break, continue
and halt. DEC assumptions are only the appropriate internal physical
register value branch. Their literal KSim target paths, overflow bits and
growth are unchanged. The source certificate establishes the physical
index bounds, so the total box interpretation's fallback is irrelevant.

start_format and target_format expose the complete numeric path, exact
distance, marker and register suffix. increment_target updates only the
selected register and appends a spare one. decrement_target updates only
the selected register, keeps the spare count and retains the extra distance
cell. These are algebraic full-tape identities, not canonical rebasing.

Checks include all nine physical bounds, both DEC branches at gap zero and
one spare, arbitrary internal values/clocks, whole payload updates and the
terminal state's preserved second projection. A concrete nonvacuous client
constructs the actual first leaf [false,false,false], DEC logical register 8
(physical 1), and executes it with zero gap, one spare and only v 1=0.

All 19 reports use standard Lean axioms only: physical_lt uses propext;
the five other finite source/bound reports use propext and Quot.sound;
the thirteen arithmetic reports use propext, Classical.choice and
Quot.sound. No sorry, native_decide, new axiom or cap increase occurs.

## Reproducible cache and attempts

The accepted plan SHA is
a2475b3256c6bdaf2cdcc25aafc7394500ab0fcdd9ae4cfdd12568096306530b,
with eleven-file manifest
29cde1cf02713dd1a8f092ec431c5de6117722a5252cff4c2dd9c36cdbc325ca.
Exact scope: 173 cached modules, including 95 Foundation modules, 458
custom artifacts, 41 boundary primaries plus 123 companions and 622 first
providers; zero dependency refresh. Accepted ROOT Home is selected from
/tmp/home215-root-gwo_lm6e/lib. The inherited source-identical, byte-unequal
KZip alternative remains explicitly recorded; the accepted current object
is retained. No Foundation or broad prerequisite build is performed.

The complete 115-line executed driver was read before execution and remains
unchanged across both attempts. It authenticates current source headers,
the reachable DAG, all pinned sources/artifacts and first providers on a
private package-only LEAN_PATH. Immutable inventory references replace a
duplicated full profile. Both input snapshots precede each attempt's first
compiler command. Fresh outputs are regular files, with pinned Lean 4.32,
-M6000 -j1 -DElab.async=false, one thread and 512MiB guards before and after
each invocation. No dependency is compiled.

Attempt 1 failed on a combined namespace-opening syntax, an explicit
startValue unfolding needed by rewrite, and one unused simp argument.
The fixes change no theorem statement or dependency. Attempt 2 passed both
leaves cleanly in 3.255 and 2.788 seconds. Main diagnostics are empty and
Checks has exactly the intended 19 reports. All two attempts, three
compiler invocations, four input snapshots, failures, commands, timings,
logs and available objects are pinned. Durable evidence copies are regular
hardlinks of immutable terminal files; no original evidence was removed.
The final driver reauthenticated 3020 observations across 1089 paths.

Final provider: /tmp/site215-controller-author-17ufgvs_/lib.

Source SHA256:

- Main: 9c3d64a9bba705e46ad8126e99cf92fef440b6514103ab5edda27f3689cd1bc3
- Checks: ca6f965e148fac20024ab04354fb9b74e7a840990a3e325131700641f1cab4ab

Object SHA256:

- Main: 1153b5306065169e5d3c9e758d4cb382c20fdcf0a3dccf522e7a82a44f8a1f81
- Checks: 0c1c83c656fe15550717abcb5ba97a494a38b7492bdb487d587b7732a0153d2d

I also authored Home, Symbolic, Boxes, Tape and earlier runtime dependencies.
This is an author receipt, not independent review of those prerequisites.
Canonical consumed-path rebasing, represented global frames, packed control
calibration, whole control/tape equivalence and its boot composition remain
later checkpoints. Source-ZFC calibration, internal polynomial/Pell witness
equivalence and the final HA proof-existence theorem remain open.

Evidence: [replay](arithmetic-site215-replay.json) and
[complete manifest](arithmetic-site215-author-replay/FILES.json).
Replay SHA256: '''+rec(F)['sha256']+'''.
''')
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),
 observations=observations,unique_paths=len(pins)),indent=2))
