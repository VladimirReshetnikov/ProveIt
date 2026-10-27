"""Freeze all ControlFrame215 attempts; retain immutable bytes using regular hardlinks."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-control-frame215-author-replay'
F=D/'reviews/arithmetic-control-frame215-replay.json'
REPORT=D/'reviews/arithmetic-control-frame215-author.md'
MARK=Path('/tmp/control-frame215-controller-author-attempts.json')
H=D/'research/c222-control-frame215-plan-20261027'
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
paths=json.loads(MARK.read_text());assert len(paths)==4
O.mkdir();attempts=[]
for number,path in enumerate(paths,1):
 p=Path(path);state=json.loads((p/'AUTHOR.json').read_text());inp=json.loads((p/'inputs.json').read_text())
 check(state['driver']);check(state['inputs']);check(inp['profile_reference'])
 assert 'profile'not in inp
 for x in inp['pins']:check(x)
 for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
 assert len(inp['actual_providers'])==640
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
 for obj in artifacts:copies.append(link(obj['path'],out/Path(obj['path']).name))
 attempts.append(dict(number=number,private=str(p),state=check(rec(p/'AUTHOR.json')),
  status=state['status'],records=state['records'],available_leaf_artifacts=artifacts,
  immutable_hardlink_copies=copies))
final=attempts[-1];assert final['status']=='PASS'
p=Path(final['private']);state=json.loads((p/'AUTHOR.json').read_text());rows=state['records']
assert len(rows)==2 and[len(x['axiom_reports'])for x in rows]==[0,20]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256']
 assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert [a['status']for a in attempts]==['FAILED','FAILED','FAILED','PASS']
assert sum(len(a['records'])for a in attempts)==6
assert[len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[467,72]
assert attempts[2]['records'][0]['object']['sha256']==rows[0]['object']['sha256']
link(MARK,O/'attempts.json');link(__file__,O/'freeze.py')
root_plan_receipt=check(rec(D/'reviews/arithmetic-control-frame215-plan-root.md'))
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and complete self-review; independent replay pending.',
 counts=state['counts'],plan=rec(H/'cache-plan.json'),plan_manifest=rec(H/'FILES.json'),
 root_plan_receipt=root_plan_receipt,final=final,attempts=attempts,provider=str(p/'lib'),
 final_sources=[x['source']for x in rows],final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],
 final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],
 reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'),
 evidence_storage='Regular hardlinks of immutable terminal metadata, inputs, logs, drivers and available leaf objects; originals retained.')
save(F,packet)
REPORT.write_text(f'''# ArithmeticControlFrame215 — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the
final 467-line main and 72-line Checks, including every proof and all final
diagnostics. The fresh final pair passed in {rows[0]['seconds']:.3f} and
{rows[1]['seconds']:.3f} seconds. Independent replay is pending. Only these new
leaves and their evidence were written; no accepted source, shared object,
shared progress document or Git state was changed.

## Exact mathematical scope

The sole imports are ArithmeticSite215 and ArithmeticControl215Table. The
actual source catalogue has exactly 4,751 entries. Control is Fin 4751;
number i = i.val + 1 is the literal one-based control key. rows_at binds
this key to the accepted packed table's exact rowOf of its source leaf.
source_walk/source_follow and resolve_source connect finite leaf syntax,
actual program traversal, canonical descent rank and the consumed path.
The latter is consume P d, including implicit zero extension, rather than
an asserted equality between an outgoing path and its next source path.

The complete physical map equality is kernel checked on Fin 9. Source
register bounds derive from the actual site checker. The internal file is
already in physical order: physical_inc/physical_decnz reconcile the source
register once, and values_write converts the exact packed-file update to
that single pointwise update. No second permutation is applied.

pcDef is a fixed Sigma0 compact lookup graph; blockDef, blocksDef,
spareDef and entryDef are fixed Sigma1 formulas declared before the model
parameters. Their realization and Delta1 instances hold in every arbitrary
ORing model of IΣ1. entryValue uses exactly nine physical register blocks,
an arbitrary internal spare count and gap, the full suffix marker, a
64-cell path area, sparse state 84 (arithmetic state 24) and left tape 1.
The lookup is total. opcode_supported separately proves that a nonzero
opcode must have an actual one-based key; arbitrary invalid keys are not
assumed live. entry_active does not imply valid control support.

outgoing_clean is the generic finite path-cleanliness theorem specialized
to each actual source leaf. Its dummy natural register vectors select a
finite DEC path only; no standard-machine simulation is used to prove any
internal execution. resolved_padded uses that Clean property, the actual
all_sites traversal/checker, the consumed length bound 48, and gap_consume.
It proves equality of the entire paths padded to 64+overflow+extra cells.
All discarded stored bits are false, and implicit extra bits are false.
path_affine and target_rebase then preserve an arbitrary internal suffix,
not merely a low path word. No numeric register, spare or gap is truncated.

The six canonical endpoints cover INC, DEC zero, DEC positive, break,
continue and halt. They compose the actual Site215 execution contracts with
the exact consumed-path rebase. INC updates the selected register and
appends one spare; DEC positive preserves the spare count and retains its
extra left blank cell. Overflow contributes its literal zero/one to the
gap. Zero gap and zero register values remain admitted; k>0 is explicit.
Every endpoint retains a positive clock from the actual moved=false site
execution. Halt means first(configuration)=0, with terminal tape payload
retained; configuration=0 is not asserted.

step_at invokes the accepted actual spec215 row semantics. entry_step
derives a new valid Control, physical file, positive spare count and gap,
with equality to the actual control step and positive tape reachability.
entry_halt derives the actual source halt case from the step result by
excluding each supported nonhalt instruction, then obtains a positive
actual tape clock. No caller supplies a successful checker, canonical
successor, table correctness or execution oracle.

Checks include invalid table keys 0 and 4752, the actual first leaf
[false,false,false]/DEC logical register 8/physical register 1, all nine
physical-map entries, zero-extension and discarded-zero path examples,
Sigma1/Delta1 interfaces, zero spare representation, live state 24,
invalid-opcode rejection and a nonvacuous first-site execution at gap zero
and one spare. Both generic k/gap and concrete zero-gap clients use the
same actual source theorem. All 20 reports are standard-only: physical_map
uses propext; the other 19 use propext, Classical.choice and Quot.sound.
There is no sorry, native_decide, new axiom or compiler-cap increase.

## Cache, provenance and attempts

The frozen approved cache plan SHA is
d0570b2d5abda25e5d4026fa9216f4e41cbb4d80ff17c91368cce973f56e595d,
with ten-file manifest
121f174d0cf117c5b336c7ec767d4dbe8053dc1dd3e89934f8b51d1b2897184e.
Exact scope: 191 cached modules, including 95 Foundation modules, 476
custom artifacts, 41 boundary primaries plus 123 companions and 640 first
providers; zero refresh. Site215 selects accepted ROOT provider
/tmp/site215-root-1ub48_h4/lib. The packed table selects accepted independent
provider /tmp/control215-table-peer-_nt2n9b9/lib. All 124 shared prerequisite
modules have identical source/artifact bytes. The inherited source-identical
but unequal KZip alternative remains recorded; the current accepted
selection is unchanged. No Foundation or prerequisite compilation occurs.

The complete executed driver was read before compilation and remained
unchanged throughout. It authenticates the complete source-header DAG,
all selected pins, compiler, boundary artifacts and actual first providers.
The private LEAN_PATH contains its pinned symlink cache and explicit package
paths, with no project shared-cache fallback. Each pair snapshots both
inputs before its first compiler command. Only fresh regular leaf outputs
are compiled, using pinned Lean 4.32, -M6000 -j1 -DElab.async=false,
one thread and 512MiB disk guards. The single immutable inventory is
referenced by path/hash rather than duplicated in each attempt profile.

All four attempts are preserved. Attempt 1 failed on explicit t215
conversion, dependent List.ofFn simplification, a definition refold,
Sigma0-to-Delta1 lifting, cast/update names and tactic layout. Attempt 2
left only the state numeral cast and symmetry of a negated equality.
Attempt 3 passed the main but Checks required an explicit Fin projection
and symbolic first_edge/first_number rewrites to avoid deep unification.
Attempt 4 passed both cleanly with an empty main log and exactly 20 reports.
The public mathematical endpoints, imports and caps were unchanged. No
failed invocation was discarded or retried by raising a limit. The third
and fourth main objects are byte-identical.

The durable packet retains all six compiler invocations, eight input
snapshots, commands, timings, full logs, available objects and every failed
record. Immutable terminal evidence and available objects are regular
hardlinks; original paths and bytes are preserved. The final driver
reauthenticated {state['final_observations']} observations across
{state['unique_paths']} paths. This freeze rehashed {observations}
observations across {len(pins)} paths.

Final provider: {p}/lib.

Source SHA256:

- Main: {rows[0]['source']['sha256']}
- Checks: {rows[1]['source']['sha256']}

Object SHA256:

- Main: {rows[0]['object']['sha256']}
- Checks: {rows[1]['object']['sha256']}

I also authored Site, Home, Symbolic, Boxes, Tape, the packed 215 table and
earlier runtime dependencies. This is an author receipt, not independent
review of those prerequisites. complemented47_review gave a scoped
source-only challenge of the rebase/instruction endpoints at intermediate
main c91347e5931be775d039d95b8037e6401efab5ea1cbea6a12e8df806e7bb05b8,
with no finding; the later main changes only resolved the cast and negated
equality elaboration. That challenge is not a full provenance or replay
review, and is not presented as final independent acceptance.

Global Related, internal clock iteration, control/tape halting equivalence
and boot composition remain later checkpoints. Source-ZFC calibration,
internal polynomial/Pell witness equivalence and the final HA proof-existence
endpoint are not asserted here.

Evidence: [replay](arithmetic-control-frame215-replay.json) and
[complete manifest](arithmetic-control-frame215-author-replay/FILES.json).
Replay SHA256: {rec(F)['sha256']}.
''')
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),
 observations=observations,unique_paths=len(pins),final_objects=[x['object']for x in rows]),indent=2))
