from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-fwd10to15-split-check';old=root/'research/current14-k215-wf-compatibility-check'
pins={'run.py':'3f83dfd7a6003f39a318d7782343a4a37f03a5a18354fee7281e9a7ff22f7742','plan.json':'43adcfd47849e71d94547694bc4faef3d8f4f7cadbb93c521716ed3fe9e89152','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes();a=json.loads((old/'plan.json').read_text());b=json.loads((p/'plan.json').read_text());assert len(b['entries'])==38 and a['entries']==b['entries'][:20] and a['external_direct']==b['external_direct']
for k in range(10,16):
 l,r,j=b['entries'][20+3*(k-10):23+3*(k-10)];assert [e['module'] for e in (l,r,j)]==[f'BusyBeaver.ZFC.KSource215Fwd{k}Left',f'BusyBeaver.ZFC.KSource215Fwd{k}Right',f'BusyBeaver.ZFC.KSource215FwdCheck{k}'];assert l['imports']==r['imports']==['BusyBeaver.ZFC.KSource215Data'] and j['imports']==['BusyBeaver.ZFC.KSource215Data',l['module'],r['module']]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd10to15-split-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','stages':38,'lean_run':False,'scope':'Six split guard only; individual checks and coherent build unproved'},indent=2))
