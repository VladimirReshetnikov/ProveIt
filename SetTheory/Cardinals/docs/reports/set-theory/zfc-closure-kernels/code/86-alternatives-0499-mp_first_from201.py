#!/usr/bin/env python3
"""Apply MP-first reset/no-dummy semantics to the independently audited 201-node DAG.
No whole-run or binary calibration proof is asserted here.
"""
from pathlib import Path
import sys,json,importlib,time,itertools,math
HERE=Path(__file__).resolve().parent;R=HERE.parent
sys.path[:0]=[str(R/'context_folds/recovered/67/research/agent_logic'),str(R/'source/Computability/BusyBeaver/Research/ZFC'),str(HERE/'mp_first_corrected/backend')]
from verify_reassociation import Decoder,read_json
from pairing_backend_experiment import execute_helper
import recover_wade_dag as recover
import full_grammar_experiment as common
import TMBuilder as backend
H=common.load_file('mp201_helper',common.REPORT/'code/08-schema-machine-rebracket_axioms.py')
n,root,oldhash=read_json(R/'context_folds/recovered/67/research/root_search/rebracket201_minimal.json')
assert n[189]==(('I',6),('N',188)) and n[188]==(('N',186),('N',187))
assert n[197]==(('N',169),('N',43))
n[189]=(('N',166),('N',187))
fresh=max(n)+1
n[197]=(('N',169),('N',fresh))
n[fresh]=(('N',41),('N',fresh+1))
n[fresh+1]=(('I',5),('N',186))
d=Decoder(n,root);n={k:v for k,v in n.items() if k in d.reached};d=Decoder(n,root)
(HERE/'mp_first_from201.json').write_text(json.dumps(dict(root=root,nodes=n),indent=2)+'\n')
# The backend assumes entry node zero. Rename bijectively, retaining original names.
order=[root]+sorted(set(n)-{root});idx={q:i for i,q in enumerate(order)}
def edge(e):
 op=e[0];x=e[1] if len(e)>1 else None
 return {'N':lambda:f'ENode {idx[x]}','I':lambda:f'EInc {x}','D':lambda:f'EDecnz {x}','B':lambda:f'EBreak {x}','C':lambda:f'EContinue {x}','H':lambda:'EHalt'}[op]()
nn={idx[q]:tuple(map(edge,n[q])) for q in order};names={idx[q]:f'mp201_{q}' for q in order};names[0]='main().0'
builder=recover.builder_from_dag(backend,nn,names)
def run(q,values):return execute_helper(builder,idx[q],values)
def P(x,y):return (x+y)*(x+y+1)//2+y
def unP(v):s=(math.isqrt(8*v+1)-1)//2;y=v-s*(s+1)//2;return s-y,y
counts={};count=0
for top,goal,stack,success in itertools.product(range(7),range(7),range(5),[False,True]):
 vals=[101,top,stack,0,goal,4*P(top,goal)+(not success),0,0,103];out=run(198,vals)
 if success and goal==1:assert out==('halt',),(vals,out)
 else:assert out==('normal',) and vals==[101,goal if success else 0,stack,0,0 if success else goal,0,0,0,103],(top,goal,stack,success,out,vals)
 count+=1
counts['full_MP']=count;count=0
for top,stack,goal,cache in itertools.product(range(3),range(26),range(3),range(4)):
 vals=[101,top,stack,0,goal,cache,0,0,103];out=run(189,vals);a,b=unP(stack)
 assert out==('normal',) and vals==[101,top,b,0,goal,a,0,0,103],(vals,out)
 count+=1
counts['NIP']=count
m=H.compile_dag(backend,nn,names);H.reextract(m,nn,names);data,labels,missing=common.normalize(m)
(HERE/'mp_first_from201_wade.tm').write_bytes(data)
report=dict(source='rebracket201_minimal.json',source_sha256=oldhash,source_nodes=len(n),metrics_root_zero_prefix_max_zero_depth_max_path_depth=d.metrics(),leaf_sites=len(d.sites),wade_states=len(set(q for q,b in m.states)),finite_register_tests=counts,all_emitted_edges_reextracted=True,missing_totalized=missing,whole_program_calibration_proved=False)
(HERE/'mp_first_from201_report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
