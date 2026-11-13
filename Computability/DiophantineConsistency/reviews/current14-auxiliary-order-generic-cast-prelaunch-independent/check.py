from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];r=root/'research';p=r/'current14-auxiliary-order-generic-cast-check';old=r/'current14-coherent-extension-refactor-retry03-runner'
pins={'run.py':'9d9306094d30286753cf401abb0a29ef2670fdc56e8945c7d24c935c1aee4746','plan.json':'4b3d8c392c4519a392df15fdf2f99bd441d74c1d986ac580f399a8e7d2e49705','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','AuxiliaryOrderAudit.lean':'c01c2c8f7e80fc85291e7ce0e24bf8782879dda9218406e3a2c2185cc6615981'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'plan.json').read_bytes()==(old/'plan.json').read_bytes() and (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes()
plan=json.loads((p/'plan.json').read_text());s=json.loads((old/'attempt01/state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==418 and s['rows'][-1]['module']=='DiophantineConsistency.CurrentAuxiliaryOrder2011' and s['rows'][-1]['compile']['exit']==1
assert [r['module'] for r in s['rows'][:417]]==[e['module'] for e in plan['entries'][:417]] and all(r['compile']['exit']==r['deps']['exit']==0 and r['compile']['stop_reason'] is None and r['deps']['stop_reason'] is None for r in s['rows'][:417]);assert len(s['base_links'])==1000
assert plan['entries'][417]['module']=='DiophantineConsistency.CurrentAuxiliaryOrder2011' and plan['entries'][417]['imports']==['DiophantineConsistency.PrimePowerOrder','DiophantineConsistency.CurrentControllerData2011'];assert set(plan['entries'][417]['imports'])<={r['module'] for r in s['rows'][:417]}
assert (p/'AuxiliaryOrderAudit.lean').read_text()=='import DiophantineConsistency.CurrentAuxiliaryOrder2011\n#print axioms DiophantineConsistency.CurrentAuxiliaryOrder2011.generator_order_succ\n#print axioms DiophantineConsistency.CurrentAuxiliaryOrder2011.generator_order\n'
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-coherent-extension-refactor-retry03-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-auxiliary-order-generic-cast-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','provider_parent':'FAILED','individually_successful_children':417,'probe_stages':2,'lean_run':False,'scope':'Point-provider observation; no coherent rebuild established'},indent=2))
