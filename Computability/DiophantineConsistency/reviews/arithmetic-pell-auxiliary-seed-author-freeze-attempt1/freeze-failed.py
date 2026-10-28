"""Freeze the two PellAuxiliarySeed attempts and reauthenticate all immutable evidence."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-pell-auxiliary-seed-author-replay';F=D/'reviews/arithmetic-pell-auxiliary-seed-replay.json';REPORT=D/'reviews/arithmetic-pell-auxiliary-seed-author.md'
MARK=Path('/tmp/pell-auxiliary-seed-controller-author-attempts.json');H=D/'research'
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
 assert len(inp['actual_providers'])==507
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
assert len(rows)==2 and[len(x['axiom_reports'])for x in rows]==[0,5]
for row in rows:
 check(row['source']);assert row['source']['sha256']==row['snapshot']['sha256'];assert row['exit_code']==0 and not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'}
assert Path(rows[0]['log']['path']).stat().st_size==0
assert [a['status']for a in attempts]==['FAILED','PASS'];assert sum(len(a['records'])for a in attempts)==3
assert[len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[281,58]
link(MARK,O/'attempts.json');link(__file__,O/'freeze.py')
root_notes=[check(rec(D/'reviews'/name))for name in ['arithmetic-pell-auxiliary-seed-plan-root.md']]
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and complete self-review; independent replay pending.',counts=state['counts'],plan=rec(H/'arithmetic-pell-auxiliary-seed-cache-plan.json'),plan_manifest=rec(H/'arithmetic-pell-auxiliary-seed-plan-FILES.json'),root_authorization=root_notes,final=final,attempts=attempts,provider=str(p/'lib'),final_sources=[x['source']for x in rows],final_objects=[x['object']for x in rows],final_reports=rows[1]['axiom_reports'],final_authentication_observations=state['final_observations'],final_authentication_unique_paths=state['unique_paths'],reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'),evidence_storage='Regular hardlinks of immutable terminal metadata, inputs, logs, drivers and available leaf objects; originals retained.')
save(F,packet)
assert 'object' not in attempts[0]['records'][0]
REPORT.write_text(f'''# ArithmeticPellAuxiliarySeed — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the
281-line main, 58-line Checks and full executed replay driver. The final pair
passed in {rows[0]['seconds']:.3f}/{rows[1]['seconds']:.3f} seconds. Main output is empty;
all five reports use only propext, Classical.choice and Quot.sound. Independent
replay remains pending. No accepted source, shared object or Git state changed.

## Exact internal arithmetic endpoint

The only imports are ArithmeticPellSquaredSeed and ArithmeticPellHalfIndex.
Every public theorem quantifies over arbitrary elements of an arbitrary-universe
IΣ1 arithmetic model. The final auxiliary_seed theorem takes only a, R and
R%4=3. In particular a=0 remains legal, and no supplied Pell norm, desired
residue, strong seed, index divisibility, CRT or positive auxiliary witness
premise occurs in that endpoint.

For c=ycoord R a, the accepted strong_seed supplies the actual f=xcoord(R*c,a)
and positive i with ycoord(R*c,a)=i*c*c and the squared norm. Set
I=delta(a)*i*c*c. Positivity and I>=2 are derived, not requested. The new
quotient_square_pair uses a genuine Sigma1 successor induction, keeping both
Q(2t)=Y(4t+1) modulo f*f and Q(2t+1)+Y(4t+3)=0 modulo f*f. The second
quotient_divisor_pair induction keeps Q(2t)=4t+1 and Q(2t+1)+4t+3=0 modulo c.
These are actual interpreted oddQuotient and coordinate functions at arbitrary
internal indices. The invariant definability obligations are discharged by the
accepted arithmetic interface. The finite private modular transport helpers
are explicitly adapted from HalfIndex; its old mod-f/signless statement is
not substituted for this mod-f*f oriented result.

phase_indices derives R>0, R=2*((R-1)/2)+1 and (R-1)/2=2*(R/4)+1 by the
actual division equation. Hence u=oddQuotient((R-1)/2,I-2) has both oriented
residues (u+c)%(f*f)=0 and (u+R)%c=0. Its positivity follows from the actual
coordinate identity xcoord(R,I-2)=I*u. The ordinate y=ycoord(R,I-2) is positive.

positive_quotient extracts o from u+c=f*f*o, proves o>0, and uses the derived
identity f*f=1+c*H to remove a c-divisible summand from u+c+R. This yields
c|(o+R). The actual T=(o+R)/c is positive and satisfies
f*f*c*T=u+c+f*f*R. The same identity establishes
u=absdiff(f*f*c*T,f*f*R+c), with the subtraction order proved first. There is
no coprimality or Chinese-remainder premise. Finally the actual norm at base
I-2, together with delta(I-2)+1=I*I, gives
I*I*u*u+y*y=1+I*I*y*y, retaining the terminal +y*y term.

The full public theorem returns all five positive witnesses f,i,T,u,y,
their exact seed/coordinate identities, both residues and both additive norms.
Checks repeat the full all-internal statement, expose both negative phases,
exercise offset a=0, and derive positive witnesses at the least admitted rank
R=3 without computing a giant Pell numeral. Five axiom reports audit all
public lemmas. The finite phase arithmetic is not a standard-Nat substitute
for the represented induction.

This closes the positive auxiliary Pell witness checkpoint for the maintained
fourteen-variable route. It does not construct outer simultaneous source
witnesses, prove a full polynomial converse or internal HA equivalence, or
supply the signed-y/carrier-m refinements of the thirteen-variable route.
Those remain separate obligations.

## Validation and provenance

Immutable plan SHA:
59de0e399ed01693294f7c5d6363287c5268797619abc9a2f4b42b0f7ebc3e35.
Five-file plan manifest SHA:
0cafc70c5112c819bd12a3a0c44fdd16eebeb289ee08957b45be06634b22a26f.
The independent ROOT authorization note and audit JSON are pinned separately;
the audit SHA is
77164779f6904ff1f6918a76200087f3a5b0d2e57a733b398f49aea10075dd66.
Exact scope is 108 cached modules, including 95 Foundation modules, 393 custom
artifacts, 38 boundary primaries plus 76 companions, 507 first providers and
zero prerequisite refresh. Only these two new leaves were compiled.

The accepted direct prerequisites were authored by ROOT (SquaredSeed) and
complemented47_review (HalfIndex). I independently reviewed/replayed SquaredSeed
previously, and supplied scoped read-only mathematical challenges of related
Pell work. This author receipt is not an independent review of my new pair.
No Foundation or Mathlib prerequisite was authored or rebuilt in this task.

The complete source-header DAG, immutable selected pins, compiler, all actual
first providers and ROOT authorization were reauthenticated. The private
LEAN_PATH contains only pinned custom symlinks and explicit package/toolchain
paths; no shared project cache fallback is used. Both full input snapshots
precede the first compiler command in each attempt. Fresh outputs are regular
files. Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false with one thread and
512MiB reserve checks. Full main, Checks and executed driver were read before
each attempt. Source statements, imports and caps stayed unchanged.

Both attempts and all three compiler invocations are retained. Attempt 1 failed
only at two unqualified odd_one references (ambiguous with the general Odd
lemma) and a simplification of 2<=3. Qualifying ArithmeticPellHalfIndex.odd_one
and deriving the numeral inequality explicitly from lt_add_one are the only
main changes before the final clean pair. Checks remained identical. There was
no first main object. No cap increase, omitted branch or assumed premise was
used. All final logs are warning/error-free and all five reports standard-only.

The final driver authenticated {state['final_observations']} observations across
{state['unique_paths']} paths. Freeze rehashed {observations} observations across
{len(pins)} paths. Input snapshots, failed diagnostics, commands, full logs,
timings and all available objects are retained as immutable regular hardlinks,
with original private paths intact. Final provider: {p}/lib.

Main source: {rows[0]['source']['sha256']}.
Checks source: {rows[1]['source']['sha256']}.
Main object: {rows[0]['object']['sha256']}.
Checks object: {rows[1]['object']['sha256']}.

Evidence: [replay](arithmetic-pell-auxiliary-seed-replay.json), SHA
{rec(F)['sha256']}, and [manifest](arithmetic-pell-auxiliary-seed-author-replay/FILES.json).
''')
files=sorted(q for q in O.rglob('*')if q.is_file())+[F,REPORT]
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins),final_objects=[x['object']for x in rows]),indent=2))
