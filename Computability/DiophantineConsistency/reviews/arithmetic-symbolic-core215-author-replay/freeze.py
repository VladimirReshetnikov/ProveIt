"""Freeze only the authorized pair, its exact cache and all seven attempts."""
from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-symbolic-core215-author-replay'
F=D/'reviews/arithmetic-symbolic-core215-replay.json'
REPORT=D/'reviews/arithmetic-symbolic-core215-author.md'
MARK=Path('/tmp/symbolic-core215-controller-author-attempts.json')
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
pins={};observations=0
def check(x):
 global observations
 y=rec(x['path']);assert y['sha256']==x['sha256'],x['path']
 if 'bytes'in x:assert y['bytes']==x['bytes'],x['path']
 pins[y['path']]=y;observations+=1;return y
def copy(p,d):
 assert not d.exists(),str(d)
 shutil.copyfile(p,d);assert rec(p)['sha256']==rec(d)['sha256'];return rec(d)
assert shutil.disk_usage('/tmp').free>=512*1024**2
assert not O.exists() and not F.exists() and not REPORT.exists()
paths=json.loads(MARK.read_text());assert len(paths)==7
O.mkdir();attempts=[]
for number,path in enumerate(paths,1):
 p=Path(path);state=json.loads((p/'AUTHOR.json').read_text());inp=json.loads((p/'inputs.json').read_text())
 check(state['driver']);check(state['inputs'])
 for x in inp['pins']:check(x)
 for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
 for x in inp['sources']:
  check(x['snapshot']);assert x['snapshot']['sha256']==x['sha256']
 for x in state['records']:
  check(x['snapshot']);check(x['log']);check(x['timing'])
  if 'object'in x:check(x['object'])
 # Keep any leaf artifact produced before a failed audit explicitly historical.
 artifacts=[]
 for src in inp['sources']:
  obj=p/'lib'/Path(*src['module'].split('.')).with_suffix('.olean')
  if obj.exists():
   assert obj.is_file()and not obj.is_symlink();artifacts.append(check(rec(obj)))
 out=O/f'attempt-{number:02}';out.mkdir();copies=[]
 for f in sorted(p.iterdir()):
  if f.is_file()and f.suffix in {'.json','.py','.lean','.log','.time'}:copies.append(copy(f,out/f.name))
 attempts.append(dict(number=number,private=str(p),state=check(rec(p/'AUTHOR.json')),
  status=state['status'],records=state['records'],available_leaf_artifacts=artifacts,copies=copies))
final=attempts[-1];assert final['status']=='PASS'
p=Path(final['private']);state=json.loads((p/'AUTHOR.json').read_text());rows=state['records']
assert len(rows)==2 and [len(x['axiom_reports'])for x in rows]==[0,15]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256']
 assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert all(a['status']=='FAILED'for a in attempts[:-1])
copy(MARK,O/'attempts.json');copy(__file__,O/'freeze.py')
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction, complete self-review and bounded private replay; independent review pending.',
 counts=state['counts'],plan=rec(D/'research/c222-symbolic-core215-plan-20261027/cache-plan.json'),
 plan_manifest=rec(D/'research/c222-symbolic-core215-plan-20261027/FILES.json'),
 final=final,attempts=attempts,provider=str(p/'lib'),final_sources=[x['source']for x in rows],
 final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],
 final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],
 reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'))
save(F,packet)
REPORT.write_text('''# ArithmeticSymbolicCore215 — author construction and replay

27 October 2026. PASS. This is controller_certificate's author self-review
and capped private replay, not an independent acceptance. Only the new
ArithmeticSymbolicCore215 and Checks sources were written. Their sole import
is the accepted ArithmeticRegisterBoxes215 main. No dependency source,
shared object, shared progress document or Git state was changed.

The complete final 467-line main and 77-line Checks were read before the
final command, including every delta from earlier attempts. The executed
115-line driver was fully read before execution; its bytes stayed fixed
throughout all seven attempts. Both inputs were snapshotted before every
attempt's first command, even when its main later failed and Checks was not
invoked. The final main source is unchanged from clean attempt 6; the last
Checks-only delta makes two exact simplification bindings explicit.

## Actual execution and representation

The public oracle_actual, sstep_actual and exec_actual conclusions concern
the literal tm215 and arithmetic215 runFrom in every ORing model of IΣ1.
Register values, gap, spare count and resulting clocks are arbitrary model
elements, including nonstandard ones. The configuration/list/branch/fuel
syntax is finite source-level syntax. Finite fuel induction composes actual
internal executions; the internal scan and spare inductions come from the
accepted Boxes packet. No supplied oracle correctness, old252 simulation,
structured IRun or standard-Nat runtime theorem enters the public endpoint.

plainTail folds the nine primary blocks followed by repeat3 6 k. Mark,
INC and DEC have the literal physical block transformations. INC retains
the appended spare 1 and k+1; positive DEC retains the extra left bit 2*L+1.
The public oracle takes k>0, supplying the following spare block for DEC0
at the last primary. Each successful oracle case proves its index is less
than 9. Invalid finite indices explicitly fall back to the plain file; this
fallback is not asserted to equal the old Nat boxList outside physical
indices. Every fallback still starts with zero, which is exactly what the
separate raw zero/read-left transition needs.

StepOk preserves the actual symbolic moved flag. Peels/recentering are
numeric equalities; self-loop scans may have zero internal length and carry
flag false. Machine bit steps carry flag true and execute exactly one step,
including final writes/moves into terminal 230. Oracle steps prove positive
clocks while retaining the checker's weaker false flag. execWith_actual is
a generic finite composition helper; exec_actual supplies sstep_actual and
starts moved=false, obtaining a positive internal clock. It is not the
invalid assertion that an arbitrary initially true moved flag yields a
positive execution.

flatTok_push and the prefix addition theorem establish literal token
normalization. normL drops only exterior zero runs whose tail is zero.
matches_actual therefore identifies the entire arithmetic configuration,
including its exact left/right zipper orientation, rather than assuming
only tape equivalence. Zero gap and zero-length runs remain legal.

The four ordinary-Nat clients plain_nat, marked_nat, increment_nat and
decrement_nat discharge the algebraic sepsR/sepsM/boxList binding left open
by Boxes, for every Nat tuple/spare count and all Fin 9 physical selectors.
They are not used to prove execution in arbitrary arithmetic models. The
only old254 theorem called in these clients is the already imported generic
numeric ArithmeticRow254.foundation_sub_nat, identifying its choice-defined
subtraction on Nat with ordinary truncated subtraction; no old254 proof or
runtime semantics is used. Numeral 6 likewise uses an explicit generic numeral
identity followed by the actual Nat numeral theorem.

Checks instantiate every main interface, invalid-index fallback, zero gap,
both head orientations, all physical INC/DEC selectors, the last primary,
DEC0 at r8 / k1, final write/right move into 230, and the moved=false versus true
boundary. Their 15 reports all contain exactly propext, Classical.choice
and Quot.sound. No sorry, native_decide, new axiom or cap increase is used.

## Exact cache and final commands

The frozen approved cache plan is
research/c222-symbolic-core215-plan-20261027/cache-plan.json,
SHA 821bf1b4e5d124858d5eb0c6d5540a37a2a2b0299e6fa385d04957890d9660aa.
It selects 148 cached custom modules, including 95 Foundation modules,
433 custom artifacts and 41 boundary primaries plus 123 companions, for 597
actual first artifact providers. All headers, reachable imports, source and
artifact pins, package-only LEAN_PATH and first providers were checked.
The accepted ROOT Boxes/Prefix provider is retained exactly as selected by
that plan. No dependency refresh or Foundation build ran.

Final private provider:
`/tmp/symbolic-core215-controller-author-3yp4zkh2/lib`.
Commands use the pinned Lean 4.32 executable with
`-M6000 -j1 -DElab.async=false -o <fresh-regular-output> <source>`,
LEAN_NUM_THREADS=1 and the 512MiB reserve before and after each command.
The main passed in 8.055 s with maximum RSS 1873728 KiB; Checks passed in 2.582 s
with maximum RSS 1832936 KiB. The main log is empty; Checks has all 15 intended
reports and no warning/error. The final driver rehashed 2618 observations
across 913 paths. Exact paths, commands, compiler pin, logs, timings, inputs,
objects and source snapshots are in the replay packet.

Final source SHA256:

- Main: 250cd6b8567d34b982d03138e872f7e0d9b21b57522c05aba6e21ee69280b92f
- Checks: d2290cad83be57f01b2f9fae3784ca4394dafe7d254736d59d420d77ac16cecc

Final object SHA256:

- Main: 8fe5cb749c1cba56a9d9549b78b8ce4cf2dece464b0e711f05e4733630f6938d
- Checks: 7dc45de9e90b8d334bdcf874bc37a3b0e40fdfeef9fa2067f259c5cd72b2ca5f

## Preserved attempts and scope

All seven attempts are retained. Attempts 1–5 failed only local Bool simp,
namespace resolution, list append normalization and Foundation-Nat numeral
or subtraction conversions. Attempt 4 deliberately enables pp.all at the
two failing clients to expose those instance distinctions; its complete log
is preserved. Attempt 6 main passed cleanly, while Checks found two local
fallback/Fin8 simplification failures. Attempt 7 is the clean full pair.
There are nine compiler invocations total; no failed attempt is described
as a successful full packet. All 14 input snapshots, every command/log/timing
and every available leaf object remain pinned. Historical source paths are
verified through their snapshots; only the final pair is compared to the
current owned sources.

I also authored the lower Tape/Boxes and substantial earlier runtime
prerequisites. This receipt does not claim independent review of them or of
this new pair. Home, actual all 4751 site contracts, canonical paths, the
control-to-tape simulation, source-ZFC calibration, internal equation/Pell
integration and final HA proof existence remain separate obligations.

Evidence: [replay](arithmetic-symbolic-core215-replay.json),
[complete manifest](arithmetic-symbolic-core215-author-replay/FILES.json).
Replay SHA256: '''+rec(F)['sha256']+'''.
''')
# Keep the receipt's line counts mechanically tied to the frozen files.
assert [len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[467,77]
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins)),indent=2))
