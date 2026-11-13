from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-wf-last-chunk-check';first=root/'research/current14-k215-wf-chunk-probe-check'
pins={'run.py':'b3961cec6eff8e7adb98ae0bba8a9bdd8377ea365600e690957b68053732157a','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','plan.json':'470b8bff5d278557f2ff5e894aa944f38e60f1af758a02e506182730b35b6dbb','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a'}
for n,h in pins.items(): assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
obs=json.loads((p/'controls-observation.json').read_text());assert obs['status']=='PASS_NON_LEAN_CONTROLS_AND_PREFLIGHT' and obs['output_absent_before_after'] and obs['sha256']==pins
assert (p/'monitor.py').read_bytes()==(first/'monitor.py').read_bytes()
entries=json.loads((p/'plan.json').read_text())['entries'];assert [e['module'].split('.')[-1] for e in entries]==['KSource215WfTables','KSource215WfChunk15'];assert entries[0]['imports']==['BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.DagPerm'] and entries[1]['imports']==[entries[0]['module']]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-last-chunk-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','lean_run':False,'scope':'Last-chunk source and guard; compilation and full wfCheck assembly open'},indent=2))
