from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-coherent-extension-refactor-runner';old=root/'research/current14-coherent-extension-runner';compat=root/'research/current14-k215-wf-compatibility-check'
pins={'run.py':'aa50f07d5dc350d30e66c45539627df66d38a187111875d604fe27924fa0463a','plan.json':'81c6db2664fb6cc574ae39e68904a21558daae4d2c3385e003fdb1cb05f0a13c','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','Current14CoherentAudit.lean':'b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes() and (p/'Current14CoherentAudit.lean').read_bytes()==(old/'Current14CoherentAudit.lean').read_bytes()
a=json.loads((old/'plan.json').read_text());b=json.loads((p/'plan.json').read_text());cp=json.loads((compat/'plan.json').read_text());A={e['module']:e for e in a['entries']};B={e['module']:e for e in b['entries']};H=[e['module'] for e in cp['entries'][:18]];target='BusyBeaver.ZFC.KSource215Data';assert len(A)==490 and len(B)==508 and all(A[n]==B[n] for n in A if n!=target) and a['external_direct']==b['external_direct'] and len(b['external_direct'])==99
names=list(B);i=names.index(target);assert names[i-18:i]==H and [n for n in names if n not in H]==list(A);assert [B[n] for n in H]==cp['entries'][:18]
e=cp['entries'][-1].copy();e['origin']=A[target]['origin'];e['old_parent_status']=A[target]['old_parent_status'];assert B[target]==e
assert sum(e['old_parent_status']=='FAILED' for e in b['entries'])==7
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-compatibility-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','project_stages':508,'audit_client':1,'prior_failed_parent_children':7,'lean_run':False,'scope':'Refactored coherent build guard; success and transitive package ancestry unproved'},indent=2))
