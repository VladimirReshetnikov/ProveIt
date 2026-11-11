from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];orig=root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean';draft=root/'research/current14-k215-wf-compatibility-draft/KSource215Data.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(orig)=='23b670c2b6ffd08fa173bbbe54faaf8989aac9b410a41a3332dee3f5fcaa5554'
assert sha(draft)=='0df977b929ba0ec031c2d6f6da1e901ffdd3cdb6141282dff556010a108ca31a'
x=orig.read_text();y=draft.read_text();imp='import BusyBeaver.ZFC.DagPerm\n';assert x.count(imp)==1
x=x.replace(imp,imp+'import BusyBeaver.ZFC.KSource215WfAssembly\n')
body='      (fun n => tC.getD n 0) = true := by\n  decide +kernel\n';assert x.count(body)==1
x=x.replace(body,body.replace('  decide +kernel','  exact SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfCheck222'))
x+='\n#print axioms SetTheory.BusyBeaver.ZFC.KSource215.wfCheck222\n#print axioms SetTheory.BusyBeaver.ZFC.KSource215.wf222\n#print axioms SetTheory.BusyBeaver.ZFC.KSource215.path_iff_iter\n'
assert x==y
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-assembly-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_ONLY','exact_deltas':'one assembly import, wfCheck proof term, three axiom reports','lean_run':False,'original_file_untouched':True,'scope':'Definitional equality and successful compilation not yet established'},indent=2))
