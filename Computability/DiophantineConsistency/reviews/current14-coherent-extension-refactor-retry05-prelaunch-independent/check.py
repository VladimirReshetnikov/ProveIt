from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];r=root/'research';p=r/'current14-coherent-extension-refactor-retry05-runner';old=r/'current14-coherent-extension-refactor-retry04-runner';wang=r/'current14-wang942core-count-split-check';draft=r/'current14-wang942core-count-split-draft'
pins={'run.py':'f025f9fdf7ec59762faab7d135bed4bff50fe841f08397c0d126f83236d3e84e','plan.json':'b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','Current14CoherentAudit.lean':'b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes() and (p/'Current14CoherentAudit.lean').read_bytes()==(old/'Current14CoherentAudit.lean').read_bytes()
a=json.loads((old/'plan.json').read_text());b=json.loads((p/'plan.json').read_text());A={e['module']:e for e in a['entries']};B={e['module']:e for e in b['entries']};target='DiophantineConsistency.WangTiles942Core';H=['DiophantineConsistency.'+n for n in ('WangTiles942CoreA','WangTiles942CountsFalse','WangTiles942CountsTrue','WangTiles942CoreB')];audit='DiophantineConsistency.Wang942CoreAudit';assert len(A)==524 and len(B)==529 and all(A[n]==B[n] for n in A if n!=target) and a['external_direct']==b['external_direct'] and len(b['external_direct'])==99
names=list(B);assert [n for n in names if n not in H+[audit]]==list(A);i=names.index(target);assert names[i-4:i]==H and names[i+1]==audit
for n in H+[target]:
 src=draft/(n.split('.')[-1]+'.lean');assert B[n]['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()
assert B[H[0]]['imports']==A[target]['imports'] and B[H[1]]['imports']==B[H[2]]['imports']==[H[0]] and B[H[3]]['imports']==H[:3] and B[target]['imports']==[H[3]] and B[audit]['imports']==[target]
assert B[audit]['source_sha256']==hashlib.sha256((wang/'Wang942CoreAudit.lean').read_bytes()).hexdigest() and B[audit]['origin']=='wang-audit';assert sum(e['old_parent_status']=='FAILED' for e in b['entries'])==7
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-wang942core-count-split-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','plan_stages':529,'endpoint_audit':1,'source_refactors':11,'prior_failed_parent_children':7,'lean_run':False,'scope':'Refactored coherent guard; completion and transitive package ancestry unproved'},indent=2))
