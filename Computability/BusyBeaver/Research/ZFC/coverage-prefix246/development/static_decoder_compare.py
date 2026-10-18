from pathlib import Path
from collections import Counter
import hashlib,json,importlib.util,sys
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');D=Path('/tmp/zfc-prefix246-lean/coverage');P=Path('/tmp/zfc-intake-8cdc55ff92/extracted/zfc-context246');F=Path('/tmp/zfc-prefix250-lean/coverage/generate_sites_prefix250.py');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
n='reviewed_decoder_parser246';spec=importlib.util.spec_from_file_location(n,F);m=importlib.util.module_from_spec(spec);sys.modules[n]=m;spec.loader.exec_module(m)
T=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ActualTree254.lean';tree=m.literal_tree(T);physical=[6,2,0,4,3,7,8,5,1];opcode={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'};sites=[]
def walk(t,p):
 if t.edge is None:walk(t.left,p+'0');walk(t.right,p+'1');return
 op,k=t.edge;sites.append([p,opcode[op],physical[k]if op in ['inc','decnz']else None if op=='halt'else k])
walk(tree,'');cached=P/'sources/prior/instruction-sites-physical.json';assert sites==json.loads(cached.read_text())
counts=Counter(q[1]for q in sites);assert len(sites)==6460 and sum(2 if q[1]=='CD'else 1 for q in sites)==8391
out={'status':'STATIC_IDENTITY_PASS','scope':'Own-code traversal of the pinned maintained literal Lean tree compared to all source63 cached sites, without running any affine checker, binary interpreter or compiler. The reviewed pure coverage parser is used only to read the literal expression.','actual_tree':{'path':str(T),'sha256':sha(T)},'parser':{'path':str(F),'sha256':sha(F)},'source63_cached_sites':{'path':str(cached),'sha256':sha(cached)},'all6460_sites_equal_in_order':True,'node_count':6459,'leaf_count':6460,'guarded_cases':8391,'max_depth':max(len(q[0])for q in sites),'min_depth':min(len(q[0])for q in sites),'physical_map':physical,'by_operation':dict(counts),'proof_status':'Static source identity, not site acceptance or a new Lean theorem. ActualTree254.tree_eq remains the separate already checked Lean program binding.'};p=D/'source63-static-decoder.json';p.write_text(json.dumps(out,indent=2)+'\n');print(p,sha(p));print(json.dumps(counts,indent=2))
