"""Freeze the five Runtime215 attempts and reauthenticate all immutable evidence."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-runtime215-author-replay';F=D/'reviews/arithmetic-runtime215-replay.json';REPORT=D/'reviews/arithmetic-runtime215-author.md'
MARK=Path('/tmp/runtime215-controller-author-attempts.json');H=D/'research/c222-runtime215-composition-plan-20261027'
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
paths=json.loads(MARK.read_text());assert len(paths)==5
O.mkdir();attempts=[]
for number,path in enumerate(paths,1):
 p=Path(path);state=json.loads((p/'AUTHOR.json').read_text());inp=json.loads((p/'inputs.json').read_text())
 check(state['driver']);check(state['inputs']);check(inp['profile_reference']);assert 'profile'not in inp
 for x in inp['pins']:check(x)
 for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
 assert len(inp['actual_providers'])==656
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
assert len(rows)==2 and[len(x['axiom_reports'])for x in rows]==[0,15]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256'];assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert [a['status']for a in attempts]==['FAILED']*4+['PASS'];assert sum(len(a['records'])for a in attempts)==6
assert[len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[159,54]
link(MARK,O/'attempts.json');link(__file__,O/'freeze.py')
root_notes=[check(rec(D/'reviews'/name))for name in ['arithmetic-runtime215-plan-root.md','arithmetic-runtime215-plan-root.json','arithmetic-runtime215-plan-root-addendum.md']]
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and complete self-review; independent replay pending.',counts=state['counts'],plan=rec(H/'cache-plan.json'),plan_manifest=rec(H/'FILES.json'),root_authorization=root_notes,final=final,attempts=attempts,provider=str(p/'lib'),final_sources=[x['source']for x in rows],final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'),evidence_storage='Regular hardlinks of immutable terminal metadata, inputs, logs, drivers and available leaf objects; originals retained.')
save(F,packet)
REPORT.write_text(f'''# ArithmeticRuntime215 — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the final
159-line main, 54-line Checks and complete executed driver. The final fresh pair
passed in {rows[0]['seconds']:.3f}/{rows[1]['seconds']:.3f} seconds, with an empty main log
and exactly 15 reports, each using only propext, Classical.choice and Quot.sound.
Independent replay is pending. No accepted source, shared object or Git state changed.

## Exact theorem and proof scope

The only imports are ArithmeticControlFrame215, ArithmeticControlBisimPerm215 and
ArithmeticDagRuntimePerm222. The public enum_blank_halts_iff is valid in every
arbitrary ORing model of IΣ1, with genuinely internal clocks on both sides:
actual ArithmeticEnumRunPerm222 from live(0,4,0) halts exactly when the first
projection of the actual literal decimal215 blank run becomes zero. Neither
side is an externally quantified Nat runtime adapter. No source-refutation,
ZFC consistency, polynomial zero, PA derivation or HA derivation is asserted here.

relatedDef is fixed Sigma1 syntax declared before model parameters. Its realization
retains a supported one-based control key through a nonzero actual opcode, physical
file, positive spare count and arbitrary gap. related_supported derives a finite
actual Control from that lookup; arbitrary nonzero scalar control codes are not
assumed valid. related_live and related_active retain logical and tape liveness.
entry_step derives a valid next source, full new file, positive spare count and
positive actual tape clock. entry_halt gives an actual positive halt clock.
The logical and binary recurrences, add law, graph definability, initialization,
successor/halt contracts and full halted-payload absorption discharge every premise
of the accepted generic PositiveSimulation254 theorem. That theorem uses its
represented Sigma1 clock invariant, not an upper clock bound or IΣ2 induction.

canonical_halts_iff admits any actual source, arbitrary internal file/gap and k>0.
Halting is first(configuration)=0; the retained terminal tape is not asserted to
be scalar zero. halt_absorbs proves the whole configuration is fixed afterward.

The seed file is already in physical order: [0,0,0,0,0,0,4,0,0], with candidate4
at register6. Its spare count is 40 and gap is 1. The exact first catalogue source
is [false,false,false]/DEC8; its canonical path bits are zero, and the 64-cell
canonical area plus gap1 gives 65 leading blanks. standard_seed_entry uses only
actual entry_format, plain_nat, prefix composition and the exact sepsR boot vector;
it does not evaluate the boot run or expand the large boot numeral. The fixed
seed graph uses the literal ORing numeral40, whose equality with the ordinary
arithmetic numeral is proved through the existing numeral/cast laws. The nine
register-list normalization is checked by the kernel.

seedEntryDef is the same fixed Sigma1 function graph in Nat and every model.
Its absoluteness transfers the exact standard seed code to the internal entry;
no informal standard/nonstandard identification is used. control_blank_halts_iff
then applies the accepted 95,714-step boot theorem and its early-halting exclusion.
The ROOT plan's prose slip 'clock40' is explicitly corrected in the separately
pinned addendum: 40 is the spare count, while 95,714 is the boot clock.

Finally, actual DagRuntimePerm222.seed_halts_iff, the certified full-table
BisimPerm215 equivalence, and the control/blank equivalence are composed in their
literal orientations. The physical file is passed unchanged; no second register
permutation, assumed root IRun, table correctness oracle, supplied simulation
relation or old concrete 252/254 runtime endpoint occurs as a premise.

Checks bind the seed vector/right tape, both fixed graph interfaces, candidate
register6, invalid control0 rejection, valid arbitrary source at gap0, full halt
payload absorption, exact internal 95,714 boot and arbitrary continuation, and
both directions of the actual Enum/decimal endpoint. All 15 reports and complete
logs are preserved. There is no sorry, native_decide, new axiom or raised cap.

## Authentication and attempts

Approved cache-plan SHA 4a93686eebfefcd2b325e88a9644e9a7aad5f8a45e4744bafb287959377ebb34;
seven-file plan manifest 6419d84589931c450ac7ea94915c50285bf0457ed14111bcd2356b55179ad4b6.
Exact scope is 207 cached modules including 95 Foundation, 492 cached custom
artifacts, 41 boundary primaries plus 123 companions, and 656 first providers.
There is zero refresh: only the two new leaves compile. The accepted ROOT Frame,
Bisim and DagRuntime selections retain all original provenance and prior shared
artifact checks; the source-identical unequal KZip alternative remains recorded,
without changing the accepted selection.

Each invocation reauthenticated the entire source-header/reachable DAG, all pins,
compiler and actual first providers. LEAN_PATH contains the isolated pinned
symlink cache and explicit package paths, with no project shared cache fallback.
Both input snapshots preceded the first compiler command of every attempt. Fresh
outputs are regular nonsymlink files; pinned Lean4.32 runs with -M6000 -j1
-DElab.async=false, one thread and 512MiB disk guards. The immutable complete
inventory is referenced rather than copied into every attempt profile.

All five attempts and six compiler invocations remain preserved. Attempt1 exposed
Foundation numeral40 versus literal Nat40 in the graph/seed rewrite, and an
unfocused absoluteness simplification reached the existing recursion limit.
Attempt2 used explicit pretty-print diagnostics, whose placement after a doc
comment also caused a syntax error; it confirmed the distinct numeral instances.
Attempt3 isolated the remaining Nat seed conversion and exposed an insufficiently
annotated cast, which Lean had elaborated as a V-valued application. Attempt4
closed those obligations using the raw numeral graph and explicit Nat result
annotation, leaving only the nine-register list normalization. Attempt5 adds its
exact kernel proof and passes both leaves cleanly. The public equivalence statements,
imports and resource caps did not change. No failure or diagnostic was discarded.

The final driver authenticated {state['final_observations']} observations across
{state['unique_paths']} paths. Freeze rehashed {observations} observations across
{len(pins)} paths. All terminal evidence and objects use regular immutable hardlinks;
original private paths remain present. Final provider: {p}/lib.

Main source: {rows[0]['source']['sha256']}.
Checks source: {rows[1]['source']['sha256']}.
Main object: {rows[0]['object']['sha256']}.
Checks object: {rows[1]['object']['sha256']}.

I also authored Frame/Site/Home/Symbolic/Boxes/Tape and the control/bisimulation/
DagRuntime prerequisites. This is an author receipt, not independent review of
those dependencies or the new composition. ROOT independent review/replay remains
required for acceptance. complemented47_review read the complete final main and
Checks and reported no source-level composition finding; that scoped challenge
did not authenticate/replay the prerequisite closure and is not independent
acceptance. Source-ZFC calibration, internal polynomial/Pell witness
translation and the final HA proof-existence endpoint remain separate obligations.

Evidence: [replay](arithmetic-runtime215-replay.json), SHA {rec(F)['sha256']},
and [complete manifest](arithmetic-runtime215-author-replay/FILES.json).
''')
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins),final_objects=[x['object']for x in rows]),indent=2))
