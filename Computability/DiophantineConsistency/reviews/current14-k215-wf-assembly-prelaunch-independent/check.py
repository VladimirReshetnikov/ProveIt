from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'research/current14-k215-wf-assembly-check';first=root/'research/current14-k215-wf-last-chunk-check'
pins={'run.py':'a27da2a7c0d0fa892515ad4eea2d37a6822d429102122a9b06daf12fad08899d','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','plan.json':'b83813e024874450ce9fcab6dc8c05269c8d97b8c988dc160ec165eee75b212c','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a'}
for n,h in pins.items(): assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(first/'monitor.py').read_bytes()
entries=json.loads((p/'plan.json').read_text())['entries'];assert len(entries)==18
assert [e['module'].split('.')[-1] for e in entries]==['KSource215WfTables']+[f'KSource215WfChunk{i:02}' for i in range(16)]+['KSource215WfAssembly']
assert entries[0]['imports']==['BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.DagPerm']
assert all(e['imports']==[entries[0]['module']] for e in entries[1:17])
assert entries[-1]['imports']==[e['module'] for e in entries[1:17]]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-assembly-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','lean_run':False,'scope':'18-stage guard and source review; assembly and original module remain uncompiled'},indent=2))
