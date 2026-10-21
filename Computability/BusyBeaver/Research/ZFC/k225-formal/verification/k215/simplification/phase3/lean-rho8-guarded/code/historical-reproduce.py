"""Own bounded renderer reproduction; no Lean/compiler invocation."""
import hashlib,json,subprocess,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
FORMAL=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal'
OUT=P/'reproduction2';OUT.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
relformal=Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
reltemplate=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/149-dom-theory-ev-CD230.v')
workspace=OUT/'workspace';cg=workspace/relformal/'generate_domrho8_lean.py';cg.parent.mkdir(parents=True)
cg.write_bytes((P/'generate_domrho8_lean.py').read_bytes())
ct=workspace/reltemplate;ct.parent.mkdir(parents=True);ct.write_bytes((ROOT/reltemplate).read_bytes())
co=OUT/'original.json';co.write_bytes((FORMAL/'lean217/dominated_rho8_full_certificate.json').read_bytes())
cr=OUT/'reduced629.json';cr.write_bytes(Path('/tmp/k215-domrho8-global629/certificate.json').read_bytes())
plan=workspace/relformal/'rho8plan/plan.json';plan.parent.mkdir()
plan.write_bytes((FORMAL/'rho8plan/plan.json').read_bytes());rp=plan.with_name('replay.py');rp.write_bytes((FORMAL/'rho8plan/replay.py').read_bytes())
inputs=[cg,ct,co,cr,plan,rp];before={str(p):sha(p) for p in inputs}
cases=[('default',co,[], '15fb9907bc3a60b69f87fc40cecf6153bf838a23ebf3c5272df9262faa9159e8'),('explicit-templates',co,['--templates',str(ct)],'15fb9907bc3a60b69f87fc40cecf6153bf838a23ebf3c5272df9262faa9159e8'),('explicit-plan',co,['--plan',str(plan)],'87f7f42765fbba7fa762e2516e115cffe64d19db17213487f5705e1b38c4959c'),('no-plan',co,['--no-plan'],'92b8ec86d4fd038755800e785a2178dd1c995267fa75d2828a55ec4e86d9c5a6'),('generic629',cr,[],'87f7f42765fbba7fa762e2516e115cffe64d19db17213487f5705e1b38c4959c')]
results=[]
for name,src,opts,want in cases:
 out=OUT/(name+'.lean');cmd=[sys.executable,'-B',str(cg),str(src),str(out),*opts];start=time.monotonic()
 r=subprocess.run(cmd,capture_output=True,timeout=30)
 (OUT/(name+'.stdout')).write_bytes(r.stdout);(OUT/(name+'.stderr')).write_bytes(r.stderr)
 row={'name':name,'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,'output_sha256':sha(out) if out.exists() else None,'expected':want}
 results.append(row)
 assert r.returncode==0 and row['output_sha256']==want,row
# Two invalid combinations must fail before producing a proof source.
for name,src,opts in [('reject-mixed-mode',co,['--templates',str(ct),'--no-plan']),('reject-generic-templates',cr,['--templates',str(ct)])]:
 out=OUT/(name+'.lean');cmd=[sys.executable,'-B',str(cg),str(src),str(out),*opts];r=subprocess.run(cmd,capture_output=True,timeout=30)
 (OUT/(name+'.stdout')).write_bytes(r.stdout);(OUT/(name+'.stderr')).write_bytes(r.stderr)
 assert r.returncode!=0 and not out.exists()
 results.append({'name':name,'command':cmd,'exit_code':r.returncode,'output_absent':not out.exists()})
after={str(p):sha(p) for p in inputs};assert before==after
api=(FORMAL/'verification/k215/simplification/phase2/rho8-global/lean/API.lean').read_text().split('\n',1)[1]
snapshot=Path('/tmp/k215-domrho8-conceptual-survey/run4/PlainWithAudit.lean')
assert (OUT/'default.lean').read_text()+'\n'+api==snapshot.read_text()
record={'status':'PASS','scope':'Five renderer modes and two invalid-mode controls; no proof kernel invoked','inputs_before':before,'inputs_after':after,'inputs_unchanged':before==after,'cases':results,'typed_snapshot':str(snapshot),'typed_snapshot_sha256':sha(snapshot),'generated_plus_five_api_clients_equals_kernel_snapshot':True}
(OUT/'result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':record['status'],'cases':len(results),'result':str(OUT/'result.json')},indent=2))
