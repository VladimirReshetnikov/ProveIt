from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];r=root/'research';p=r/'current14-splitgeometry59-quadratic-partition-check';old=r/'current14-coherent-extension-refactor-retry02-runner'
pins={'run.py':'2ae635ce931d6c867e4f5212ac5527804047ab111329df4740ba10add174857b','plan.json':'659c292bd3a54de7745c5a9173c92872932c16c4f9574de0a8d695a0d7641ebf','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','Current14CoherentAudit.lean':'b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e','SplitGeometry59Audit.lean':'2e18db0a5bb47d00d42ae3f9099a3e9f8069bf977045d785f80c82c58209b29a'}
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert (p/'monitor.py').read_bytes()==(old/'monitor.py').read_bytes() and (p/'plan.json').read_bytes()==(old/'plan.json').read_bytes()
plan=json.loads((p/'plan.json').read_text());entries=plan['entries'];assert len(entries)==522 and entries[124]['module']=='DiophantineConsistency.SplitGeometry59' and sum(e['old_parent_status']=='FAILED' for e in entries[:125])==4
client=(p/'SplitGeometry59Audit.lean').read_text();assert client=='import DiophantineConsistency.SplitGeometry59\n#print axioms DiophantineConsistency.SplitCertificate59.linear_cross\n#print axioms DiophantineConsistency.SplitCertificate59.quadratic_cross\n#print axioms DiophantineConsistency.SplitCertificate59.targetPositions_range\n'
code=(p/'run.py').read_text();assert "if require_fresh:need(shutil.disk_usage('/tmp').free>=5_250_000_000" in code and "entries=list(plan['entries'][:125])" in code and "need(len(completed)==126" in code
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-splitgeometry59-quadratic-partition-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_PRELAUNCH_REVIEW','stages':126,'startup_free_minimum_bytes':5250000000,'runtime_stop_bytes':5100000000,'lean_run':False,'scope':'Partition feasibility guard; coherent endpoint and target compilation open'},indent=2))
