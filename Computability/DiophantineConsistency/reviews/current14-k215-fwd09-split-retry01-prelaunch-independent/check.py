from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-fwd09-split-retry01-check';old=root/'research/current14-k215-fwd09-split-check'
pins={'run.py':'276e8264c6345e9e10daa5c0c2ecb05a8507c1cb6f5ed8b74dcf34a7648094cc','plan.json':'20a3d72344b251484b5fddda58a1cb484b79b5c49d704eb311db9e710f8b78ce','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes();a=json.loads((old/'plan.json').read_text());b=json.loads((p/'plan.json').read_text());assert len(a['entries'])==len(b['entries'])==23 and a['entries'][:20]==b['entries'][:20] and a['external_direct']==b['external_direct']
for x,y in zip(a['entries'][20:],b['entries'][20:]):assert x['module']==y['module'] and x['imports']==y['imports'] and x['origin']==y['origin']
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd09-split-retry01-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','stages':23,'lean_run':False,'scope':'Fresh split retry guard; join uncompiled'},indent=2))
