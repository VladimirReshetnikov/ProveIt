"""Freeze independent SquaredSeed replay; no source or dependency changes."""
from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';V=D/'reviews'
P=Path('/tmp/pell-squared-seed-controller-peer-n40xllwf');O=V/'arithmetic-pell-squared-seed-peer-replay'
OUT=V/'arithmetic-pell-squared-seed-peer-replay.json';REPORT=V/'arithmetic-pell-squared-seed-peer.md'
pins={};observations=0
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def check(x):
 global observations
 a=rec(x['path']);assert a['sha256']==x['sha256'],x['path'];pins[a['path']]=a;observations+=1;return a
def link(src,dst):
 src=Path(src);assert src.is_file()and not src.is_symlink()and not dst.exists()
 os.link(src,dst);assert not dst.is_symlink();return check(rec(dst))
assert shutil.disk_usage('/tmp').free>=512*1024**2
assert not O.exists()and not OUT.exists()and not REPORT.exists()
s=json.loads((P/'state.json').read_text());assert s['status']=='PASS'
i=json.loads((P/'inputs.json').read_text());check(s['inputs']);check(s['driver']);check(s['author_packet'])
for key in ['profile_reference','scope','providers','authentication','compiler']:check(i[key])
for x in json.loads(Path(i['authentication']['path']).read_text())['pins']:check(x)
providers=json.loads(Path(i['providers']['path']).read_text());assert len(providers)==498
for x in providers:check(x['expected']);check(x['actual'])
rows=s['records'];assert len(rows)==2
for row,n in zip(rows,[0,4]):
 for key in ['source','snapshot','object','log','timing','author_object']:check(row[key])
 assert row['command'][1:4]==['-M6000','-j1','-DElab.async=false']and row['exit_code']==0
 assert row['object_byte_identical']and row['full_log_identical']
 assert not Path(row['object']['path']).is_symlink()
 txt=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error|sorryAx)\b',txt)
 assert len(row['axiom_reports'])==n
 for _,ax in row['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'}
assert [len(Path(x['source']['path']).read_text().splitlines())for x in rows]==[105,30]
assert json.loads(Path('/tmp/pell-squared-seed-controller-peer-runs.json').read_text())==[str(P)]
O.mkdir();copies=[]
for src in sorted(P.iterdir()):
 if src.is_file():copies.append(link(src,O/src.name))
for src in sorted((P/'logs').iterdir()):copies.append(link(src,O/src.name))
for row in rows:copies.append(link(row['object']['path'],O/Path(row['object']['path']).name))
link(__file__,O/'freeze.py')
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',reviewer='controller_certificate',author='ROOT',scope='Independent full new-source and relevant proof-binding review, exact author provenance/DAG/provider authentication and two fresh leaf replay; no source changes.',author_packet=s['author_packet'],counts=i['counts'],private_provider=str(P/'lib'),records=rows,inputs=rec(P/'inputs.json'),driver=rec(P/'driver.py'),final_state=rec(P/'state.json'),plan=i['profile_reference'],compiler=i['compiler'],LEAN_PATH=i['LEAN_PATH'],pre_and_post_authentication_observations=s['observations'],observed_paths=s['observed_paths'],freeze_authentication=rec(O/'reauthentication.json'),immutable_copies=copies,freeze=rec(O/'freeze.py'),author_attempts_preserved=2,peer_attempts=1)
save(OUT,packet)
REPORT.write_text(f'''# ArithmeticPellSquaredSeed — independent peer review

27 October 2026. PASS, no findings or requested source changes. ROOT authored
this pair; controller_certificate independently read all 105 main and 30 Checks
lines, the complete author receipt, plan/proposal, planner, author replay/freeze
drivers, prior failed diagnostic and independent executed driver. I also reread
the complete represented Recurrence and Periodicity sources supplying the actual
addition/doubling/norm/growth bindings, and checked the induction/parity scope.

The two fresh private leaves passed in {rows[0]['seconds']:.3f}/{rows[1]['seconds']:.3f} seconds.
Both objects and complete logs are byte-identical to the author's final objects
and logs. The main log is empty; all four reports use precisely propext,
Classical.choice and Quot.sound. No warnings, errors, sorry, new axioms or cap
changes occurred. I wrote only independent review/evidence files, not sources,
shared objects or Git state.

## Mathematical assessment

The represented Pell coordinates have offset base a+2 and discriminant
(a+1)(a+3), for arbitrary internal a including zero. The new even-block
invariant existentially supplies two nonnegative internal quotients. Its actual
Sigma1 definability obligation is discharged before IΣ1 successor induction;
no induction over external naturals or unrestricted predicates is substituted.
I checked both explicit successor polynomials against the existing addition
formulas and doubled-coordinate identities. They preserve the full linear
term 2*n*xcoord(R,a)*ycoord(R,a), not just a residue assertion.

The odd-block proof adds one R-step and replaces d*d by 1+delta*c*c using
the actual norm. All quotient expressions remain natural and nonnegative.
Internal parity of c=ycoord(R,a), with arbitrary internal half-index n, then
gives c² dividing ycoord(R*c,a): quotient d+s in the even branch, and 1+s
for the odd branch's already-derived quotient. This includes R=0 and c=0,
without cancellation of c or a false positive-divisor premise.

For strong_seed, R>0 and the actual time≤ordinate law give c>0, R*c>0
and positive target ordinate. The obtained quotient cannot be zero, so i>0;
one_le_x supplies f>0. The same actual norm at the explicit index R*c yields
f*f=1+delta*(i*c*c)*(i*c*c), with both coordinate equalities exposed. No desired
divisibility, standard index, arbitrary-modulus pigeonhole principle, cofinal
seed or extra model predicate is assumed. The theorem constructs this strong
seed only; it does not supply simultaneous outer/auxiliary witnesses or a full
polynomial converse, and does not assert a PA/HA proof-existence endpoint.

## Provenance and replay

Frozen author packet: 7c0e54bd7a003d21fe54dc66216e025e549e410e90547ab1f33e48ad69618f40.
Its 25-file manifest a72448ab814f6eeb1fc06cb8dece3771311e1ab0628da40bf336203b89ddf1eb
and receipt SHA 0808d17e625b71db18033ce3af1565066c00b98560f4352ea73b767469fe7090 were
reauthenticated. Both author attempts, all source snapshots, commands, timings,
logs, objects and the complete freeze observations were checked. Historical
working-source hashes are checked against their exact pre-command snapshots,
not incorrectly compared with the final edited source. The first author's
failure was only the local c abbreviation in the final norm rewrite; the
explicit change/rw repair preserves the public theorem and mathematical scope.

The sole import is ArithmeticPellPeriodicity. The exact reachable source-header
DAG has 99 cached modules, including 95 Foundation, 384 custom artifacts,
38 external primaries plus 76 companions (114 boundary artifacts), and 498
actual first providers. Zero dependencies were refreshed. All complete plan
pins, source/import lists, source/object selections, boundary artifacts and
actual first search providers were rehashed before execution; the two target
modules are absent from the reused cache. The source-authorized 99-module plan
is bc4e5d0235e3948bfac8deee9c864df2ae98c98672ac530316076da40df44be1 and its
three-file manifest is a84157fd3b381805ecfc8a29e208a59c18b426b5e87d57dc256c5a6b23ecd589.

Both new input snapshots preceded the first command. The isolated LEAN_PATH
uses the pinned custom symlinks plus explicit package/toolchain directories,
without shared project-cache fallback. Both outputs are fresh regular files.
Pinned Lean4.32 ran -M6000 -j1 -DElab.async=false, one thread, with 512MiB
reserve guards. There was one peer attempt and no peer diagnostic or failure.
The driver made {s['observations']} hash comparisons across {s['observed_paths']} paths;
freeze rechecked {observations} comparisons across {len(pins)} paths. Terminal
evidence and objects are retained through regular hardlinks, with original
private paths unchanged.

Main source: {rows[0]['source']['sha256']}.
Checks source: {rows[1]['source']['sha256']}.
Main object: {rows[0]['object']['sha256']}.
Checks object: {rows[1]['object']['sha256']}.
Private provider: {P}/lib.

I authored neither this pair nor its four Pell or Foundation prerequisites.
I previously independently reviewed/replayed Periodicity; that accepted object
is the explicitly recorded selected provider. This review reuses authenticated
prerequisites and makes no claim to freshly rebuild their closure.

Evidence: [peer replay](arithmetic-pell-squared-seed-peer-replay.json), SHA
{rec(OUT)['sha256']}, and [manifest](arithmetic-pell-squared-seed-peer-replay/FILES.json).
''')
files=sorted(x for x in O.rglob('*')if x.is_file())+[OUT,REPORT]
save(O/'FILES.json',[dict(rec(x),path=str(x.relative_to(R)))for x in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(receipt=rec(REPORT),packet=rec(OUT),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins)),indent=2))
