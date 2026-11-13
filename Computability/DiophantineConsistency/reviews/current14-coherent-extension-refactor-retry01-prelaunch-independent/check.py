from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];r=root/'research';p=r/'current14-coherent-extension-refactor-retry01-runner';old=r/'current14-coherent-extension-runner';wf=r/'current14-k215-wf-compatibility-check';fw=r/'current14-k215-fwd09-split-retry01-check'
pins={'run.py':'fdd4b52aa5a31de9eb67c61f662ccf403058517f0f1f40ce0d797b831cd15a06','plan.json':'0f53ced0291c1c980fbddd9a16368eca441dfa304ccf8d18ca4a4210219b4f9d','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','Current14CoherentAudit.lean':'b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes() and (p/'Current14CoherentAudit.lean').read_bytes()==(old/'Current14CoherentAudit.lean').read_bytes()
a=json.loads((old/'plan.json').read_text());b=json.loads((p/'plan.json').read_text());w=json.loads((wf/'plan.json').read_text());f=json.loads((fw/'plan.json').read_text());A={e['module']:e for e in a['entries']};B={e['module']:e for e in b['entries']};H=[e['module'] for e in w['entries'][:18]];F=[e['module'] for e in f['entries'][-3:-1]];targets={'BusyBeaver.ZFC.KSource215Data','BusyBeaver.ZFC.KSource215FwdCheck09'}
assert len(A)==490 and len(B)==510 and all(A[n]==B[n] for n in A if n not in targets) and a['external_direct']==b['external_direct'] and len(b['external_direct'])==99
names=list(B);assert [n for n in names if n not in H+F]==list(A);i=names.index('BusyBeaver.ZFC.KSource215Data');j=names.index('BusyBeaver.ZFC.KSource215FwdCheck09');assert names[i-18:i]==H and names[j-2:j]==F;assert [B[n] for n in H]==w['entries'][:18] and [B[n] for n in F]==f['entries'][-3:-1]
for target,src in [('BusyBeaver.ZFC.KSource215Data',w['entries'][-1]),('BusyBeaver.ZFC.KSource215FwdCheck09',f['entries'][-1])]:
 e=src.copy();e['origin']=A[target]['origin'];e['old_parent_status']=A[target]['old_parent_status'];assert B[target]==e
assert sum(e['old_parent_status']=='FAILED' for e in b['entries'])==7
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd09-split-retry01-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','project_stages':510,'audit_client':1,'prior_failed_parent_children':7,'lean_run':False,'scope':'Twice proof-refactored coherent build guard; completion and transitive package ancestry unproved'},indent=2))
