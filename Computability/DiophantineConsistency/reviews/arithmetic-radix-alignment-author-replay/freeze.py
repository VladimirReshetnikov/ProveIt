"""Freeze the two RadixAlignment attempts and reauthenticate all immutable evidence."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-radix-alignment-author-replay';F=D/'reviews/arithmetic-radix-alignment-replay.json';REPORT=D/'reviews/arithmetic-radix-alignment-author.md'
MARK=Path('/tmp/radix-alignment-controller-author-attempts.json');H=D/'research'
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
 assert len(inp['actual_providers'])==474
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
assert len(rows)==2 and[len(x['axiom_reports'])for x in rows]==[0,8]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256'];assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert [a['status']for a in attempts]==['FAILED','PASS'];assert sum(len(a['records'])for a in attempts)==3
assert[len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[126,50]
link(MARK,O/'attempts.json');link(__file__,O/'freeze.py')
root_notes=[check(rec(D/'reviews'/name))for name in ['arithmetic-radix-alignment-plan-root.md']]
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and complete self-review; independent replay pending.',counts=state['counts'],plan=rec(H/'arithmetic-radix-alignment-cache-plan.json'),plan_manifest=rec(H/'arithmetic-radix-alignment-plan-FILES.json'),root_authorization=root_notes,final=final,attempts=attempts,provider=str(p/'lib'),final_sources=[x['source']for x in rows],final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'),evidence_storage='Regular hardlinks of immutable terminal metadata, inputs, logs, drivers and available leaf objects; originals retained.')
save(F,packet)
assert 'object' not in attempts[0]['records'][0]
REPORT.write_text(f'''# ArithmeticRadixAlignment — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the
126-line main, 50-line Checks and full executed replay driver. The final
pair passed in {rows[0]['seconds']:.3f}/{rows[1]['seconds']:.3f} seconds. Main output is empty;
all eight reports use only propext, Classical.choice and Quot.sound. ROOT
independent replay remains pending. No accepted source, shared object or Git
state was changed.

## Exact internal arithmetic endpoint

The only imports are Foundation.FirstOrder.Arithmetic.Exponential.Log and
Mathlib.Tactic.Ring. Every theorem quantifies over arbitrary elements of an
arbitrary-universe IΣ1 arithmetic model. There is no standard-index or external
prime-factorization premise.

block_quotient uses genuine Sigma1 successor induction to construct z with
exp(d*n)=1+(exp(d)-1)*z. Its successor witness is 1+exp(d)*z, and its base
retains d=0. No complete-lattice or unbounded external-search existence is used.
The definability obligation for the existential exponential graph is discharged
in the actual accepted arithmetic syntax interface.

exp_mod_radix uses actual div_add_mod, the block witness, exp_add and the
positive-modulus remainder theorem. aligned_remainder assumes d>=2 and a
literal exp(u)=(exp(d)-1)*J+1. The proof establishes beta>1, bounds exp(u%d)
by beta, excludes its equality-to-beta case because that would have residue
zero, and then obtains exp(u%d)=1 and u%d=0 by exponential injectivity.
aligned_exponent derives a positive block count when J>0. The d>=2 condition
supports this residue proof; no claim that it is the weakest possible hypothesis
of the final factor theorem is made.

exponential_factor uses actual Pow2.of_dvd and exponential_of_pow2 at log(q).
The full public factor_alignment takes only d>=2, J>0 and the actual equality
exp(R)=w*((exp(d)-1)*J+1). It derives 0<w and a positive internal N with
(exp(d)-1)*J+1=exp(d*N), d*N<=R, and w=exp(R-d*N). The exponent bound is
proved from positive-divisor order before the truncated subtraction is used;
then exp_add and positive cancellation give the exact remaining factor.
There is no desired exponent-divisibility or positivity oracle.

Checks cover all-internal arbitrary-universe inputs, the zero-d block quotient,
J unrestricted in the remainder theorem, unit divisors, the full public endpoint,
and incompatibility of zero rank with a positive coefficient. The ordinary-Nat
modulus-one check documents why the residue-one proof needs beta>1. It is a
finite boundary check, not an arithmetic-model proof substitute.

This pair does not derive the literal current polynomial's zero-to-power
premises, native population/word/carry/tableau soundness, converse simultaneous
witnesses, a closed arithmetic theorem, or the final HA endpoint. Those remain
separate clients; this is the generic factor and exponent-alignment checkpoint.

## Validation and provenance

The immutable plan SHA is
4c995d04b1f5a0f3bd72e068b7232d8f57f3f485f671f78dfc4a372c1b972558;
its three-file manifest is
1627cfdfd40263656730a21e606daec8d59d3bf545a032082014e5fb34138d3c.
The separate ROOT authorization note is pinned. Exact scope is 90 cached
Foundation modules, 360 custom artifacts, 38 boundary primaries plus 76
companions, 474 first providers and zero prerequisite refresh. Only these two
new leaves were compiled. I authored none of these Foundation or Mathlib
prerequisites; my earlier independent proposal/provider review is separate
from this author construction.

The complete source-header DAG, immutable selected pins, compiler, actual first
providers and ROOT authorization were reauthenticated. The private LEAN_PATH
contains only pinned custom symlinks and explicit package/toolchain paths;
there is no shared project cache fallback. Both complete input snapshots precede
the first compiler command in each attempt. Fresh outputs are regular files.
Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false with one thread and 512MiB
reserve checks. Full main/Checks/driver bytes were read before each attempt.

Both attempts and all three compiler invocations are retained. The first main
failed solely because unqualified lt_irrefl was ambiguous between the general
and arithmetic names. Qualifying it as Arithmetic.lt_irrefl is the only source
delta before the clean final pair. The intended statement, imports, caps and
mathematical argument were unchanged. No first main object was produced.
All final logs are warning/error-free, and all eight reports are standard-only.

Complemented47_review read the entire draft pair and challenged the exact
quotient, residue boundary and final cancellation route, reporting no finding.
That was a scoped source-only challenge, with no provenance or compiler claim.
This author receipt does not stand in for the requested independent replay.

The final driver authenticated {state['final_observations']} observations across
{state['unique_paths']} paths. Freeze rehashed {observations} observations across
{len(pins)} paths. Input snapshots, failed diagnostics, commands, full logs,
timings and all available objects are retained as immutable regular hardlinks,
with the original private paths intact. Final provider: {p}/lib.

Main source: {rows[0]['source']['sha256']}.
Checks source: {rows[1]['source']['sha256']}.
Main object: {rows[0]['object']['sha256']}.
Checks object: {rows[1]['object']['sha256']}.

Evidence: [replay](arithmetic-radix-alignment-replay.json), SHA
{rec(F)['sha256']}, and [manifest](arithmetic-radix-alignment-author-replay/FILES.json).
''')
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins),final_objects=[x['object']for x in rows]),indent=2))
