from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-wf-compatibility-check';old=root/'research/current14-k215-wf-assembly-check'
pins={'run.py':'ab47719aa34a086dc3712fab70719d2866ca023efc0994b0b45b16bb7d352a4d','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','plan.json':'a5c9ff7db8797261682e99d6c2c17ef4ffc831923a1529dbe17cbe57cf473adf','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes()
e=json.loads((p/'plan.json').read_text())['entries'];prior=json.loads((old/'plan.json').read_text())['entries'];assert e[:18]==prior and len(e)==20
assert e[18]['module']=='BusyBeaver.ZFC.RMNormalizedBisim' and e[18]['imports']==['BusyBeaver.ZFC.RMBisim']
assert e[19]['module']=='BusyBeaver.ZFC.KSource215Data' and e[19]['origin']=='compat' and e[19]['imports']==['BusyBeaver.ZFC.KSource215Program','BusyBeaver.ZFC.RMNormalizedBisim','BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.DagPerm','BusyBeaver.ZFC.KSource215WfAssembly']
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-compatibility-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','lean_run':False,'scope':'20-stage guard only; compatibility compilation and coherent endpoint open'},indent=2))
