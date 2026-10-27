"""Read-only final reauthentication and manifest; never builds or creates an overlay."""
from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');H=Path(__file__).resolve().parent
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
assert shutil.disk_usage('/tmp').free>=512*1024**2
plan=json.loads((H/'cache-plan.json').read_text());obs=0;pins={}
for x in plan['authenticated_pins']+[p['provider']for p in plan['first_providers']]:
 a=rec(x['path']);assert a['sha256']==x['sha256'];pins[a['path']]=a;obs+=1
for x in [plan['proposal'],plan['planner']]:assert rec(x['path'])['sha256']==x['sha256']
assert plan['counts']['selected_first_artifact_providers']==656
assert all(plan[k]['packet']['sha256']for k in ['accepted_frame','accepted_runtime','accepted_bisim'])
save(H/'freeze-authentication.json',dict(status='PASS_READ_ONLY',observations=obs,unique_paths=len(pins),
 pins=list(pins.values()),plan=rec(H/'cache-plan.json'),free_bytes=shutil.disk_usage('/tmp').free))
(H/'README.md').write_text(f'''# Actual scheduler / decimal215 composition plan

Read-only metadata audit PASS. The proposed ArithmeticRuntime215 pair
would instantiate the accepted positive-clock transport with its actual
represented canonical relation, bind control1 and the physical NP4 file
to k40/gap1 and the accepted boot code, then compose accepted runtime and
control bisimulation to the actual decimal215 blank run.

The exact selected closure is 207 cached modules, 95 Foundation, 492
custom artifacts, 41 boundary primaries plus 123 companions, 656 actual
selected providers and zero refresh. All three direct mains select accepted
ROOT objects. The earlier PositiveSimulation refresh is retained as
historical provenance; its accepted current object is now cached reuse.
All shared artifact bytes match. The older unequal KZip alternative remains
explicit in the inherited Frame inventory, without changing its selection.

The planner recomputes the complete source-header DAG, authenticates the
accepted packets/manifests and every source/artifact, checks all overlaps
and confirms actual package-boundary precedence. It creates no overlay or
compiler job. Final freeze made {obs} observations on {len(pins)} paths;
the 512MiB reserve remained satisfied.

- Proposal SHA256: {rec(H/'PROPOSAL.md')['sha256']}.
- Inventory SHA256: {rec(H/'cache-plan.json')['sha256']}.
- Planner SHA256: {rec(H/'planner.py')['sha256']}.

Source-ZFC interpretation, internal equation/Pell witnesses and the final
HA proof-existence theorem remain separate. The proposed pair also keeps
the later closed-sentence/completeness client explicit. This plan is not
itself a proof or permission to compile; ROOT must review its exact scope.
No existing source, accepted cache, shared document or Git state changed.
''')
files=sorted(p for p in H.iterdir()if p.is_file()and p.name!='FILES.json')
save(H/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(status='PASS',files=len(files),manifest=rec(H/'FILES.json'),
 plan=rec(H/'cache-plan.json'),proposal=rec(H/'PROPOSAL.md'),observations=obs,unique_paths=len(pins)),indent=2))
