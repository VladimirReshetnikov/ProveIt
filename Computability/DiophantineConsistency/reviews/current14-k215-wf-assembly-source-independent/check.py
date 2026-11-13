from pathlib import Path
import hashlib,re,json,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-k215-wf-assembly-draft';p=Path(__file__).parent
pins=json.loads((p/'source-pins.json').read_text());assert len(pins)==18
for name,h in pins.items():assert hashlib.sha256((d/name).read_bytes()).hexdigest()==h,name
assert {x.name for x in d.glob('*.lean')}==set(pins)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-chunk-probe-source-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
assert (d/'KSource215WfTables.lean').read_bytes()==(root/'research/current14-k215-wf-chunk-probe-draft/KSource215WfTables.lean').read_bytes()
predicate=r'RMEquiv\.nodeOkb DagPerm\.dagPerm 487\s+\(fun n => tH\.getD n 0\) \(fun n => tB\.getD n 0\) \(fun n => tC\.getD n 0\)'
covered=[]
for i in range(16):
 s=(d/f'KSource215WfChunk{i:02}.lean').read_text();start=32*i;length=32 if i<15 else 7
 assert re.findall(r'^import (\S+)',s,re.M)==['BusyBeaver.ZFC.KSource215WfTables']
 assert re.search(rf"theorem wfChunk{i:02} : \(List\.range' {start} {length}\)\.all\s+\({predicate}\) = true := by\s+decide \+kernel",s)
 assert f'#print axioms SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfChunk{i:02}' in s
 covered.extend(range(start,start+length))
assert covered==list(range(487))
s=(d/'KSource215WfAssembly.lean').read_text();assert re.findall(r'^import (\S+)',s,re.M)==[f'BusyBeaver.ZFC.KSource215WfChunk{i:02}' for i in range(16)]
assert re.search(r'theorem wfNodes \(n : Nat\) \(hn : n < 487\) :\s+'+predicate+r' n = true',s)
for i in range(16):
 start=32*i;length=32 if i<15 else 7
 assert f"have hm : n ∈ List.range' {start} {length} := by" in s
 assert f'exact (List.all_eq_true.mp wfChunk{i:02}) n hm' in s
 if i<15:assert f'by_cases h{i:02} : n < {start+length}' in s
assert re.search(r'theorem wfCheck222 :\s+RMEquiv\.wfCheck DagPerm\.dagPerm 487 \(fun n => tH\.getD n 0\) \(fun n => tB\.getD n 0\)\s+\(fun n => tC\.getD n 0\) = true',s)
for term in ['decide (DagPerm.dagPerm.root < 487)','decide ((fun n => tH.getD n 0) DagPerm.dagPerm.root ≤ 487 + 1)','decide ((fun n => tB.getD n 0) DagPerm.dagPerm.root = 0)','decide ((fun n => tC.getD n 0) DagPerm.dagPerm.root = 0)','exact wfNodes n (List.mem_range.mp hn)','simpa only [RMEquiv.wfCheck, hall, Bool.and_true] using roots']:assert term in s,term
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
print(json.dumps({'status':'PASS_SOURCE_ONLY','modules':18,'chunks':16,'covered_indices':'0..486 exactly once','root_conditions':4,'original_module_refactor':False,'lean_run':False},indent=2))
