from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2]; p=root/'research/current14-k215-wf-chunk-probe-check'
pins={'run.py':'8671cbb8aedbc97bce7ec6cf7f05d9b2e17177c28e2cda3c167ba3f21543164c','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','plan.json':'f4350f4c660c69b0eaab67d0fccd434b7ab77c2dacf55e605a4a8fe8fd751d35','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','controls-observation.json':'5ccc2d9640ce025079751325dc652a2200306f09107858dc6c6d8bb45298d39b'}
for n,h in pins.items(): assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-chunk-probe-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
plan=json.loads((p/'plan.json').read_text()); entries=plan['entries']; assert [e['module'].split('.')[-1] for e in entries]==['KSource215WfTables','KSource215WfChunk00']; assert entries[0]['imports']==['BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.DagPerm']; assert entries[1]['imports']==[entries[0]['module']]
obs=json.loads((p/'controls-observation.json').read_text());assert obs['status']=='PASS_NON_LEAN_CONTROLS_AND_PREFLIGHT';assert all(obs['sha256'][k]==pins[k] for k in obs['sha256']);assert obs['commands']['controls']['exit']==obs['commands']['preflight']['exit']==0
assert (p/'monitor.py').read_bytes()==(root/'research/current14-coherent-extension-runner/monitor.py').read_bytes()
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','lean_run':False,'scope':'Source and two-stage guard only; no compilation or wfCheck assembly.'},indent=2))
