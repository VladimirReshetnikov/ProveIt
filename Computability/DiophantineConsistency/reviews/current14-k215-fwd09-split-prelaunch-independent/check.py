from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-fwd09-split-check';old=root/'research/current14-k215-wf-compatibility-check'
pins={'run.py':'bca2e6daf18572bc323ff864faefd3eccbcb87033a8a4c14638a0ef823b6ab68','plan.json':'4c8f538cf2ccbd609cb4b6a1b7d4eeda03a91bc0b94c9b978a1cb89977842774','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes()
a=json.loads((old/'plan.json').read_text());b=json.loads((p/'plan.json').read_text());assert len(b['entries'])==23 and a['entries']==b['entries'][:20] and a['external_direct']==b['external_direct'];L,R,J=b['entries'][-3:];assert [e['module'] for e in (L,R,J)]==['BusyBeaver.ZFC.KSource215Fwd09Left','BusyBeaver.ZFC.KSource215Fwd09Right','BusyBeaver.ZFC.KSource215FwdCheck09'];assert L['imports']==R['imports']==['BusyBeaver.ZFC.KSource215Data'];assert J['imports']==['BusyBeaver.ZFC.KSource215Data',L['module'],R['module']]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd09-split-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','stages':23,'lean_run':False,'scope':'Split guard only; actual kernel feasibility and coherent build unproved'},indent=2))
