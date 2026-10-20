"""Independent stored-runtime integrity/coverage audit, not a fresh induction replay."""
from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;P=H
sys.path.insert(0,str(P));import check224 as c

def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

D=Path(sys.argv[1])if len(sys.argv)>1 else H/'results';r=json.loads((D/'proof.json').read_text())
need(r['status']=='FULL_UNBOUNDED_RUNTIME_AND_EXACT_STARTUP_PASS','Incomplete runtime receipt')
need(r['engine_sha256']==sha(P/'vendor/symbolic_runtime.py')=='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145','Proof engine')
need(r['helper_sha256']==sha(P/'vendor/independent_runtime.py')=='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346','Runtime helper')
need(r['driver_sha256']==sha(H/'verify222.py'),'Fresh driver')
for field,name in [('table_sha256','candidate.tm'),('legacy_table_sha256','candidate.legacy.tm'),('source_sha256','sites.json'),('cases_sha256','cases.json')]:need(r[field]==sha(D/name),('Input/output hash',name))
T,st,halt,Q=c.parse(D/'candidate.tm');U,ust,uhalt,UQ=c.parse(D/'candidate.legacy.tm')
need((st,halt,ust,uhalt)==(0,254,95,254),'Entry/halting labels')
need(len(Q)==r['working_states'] and len(T)==r['rows']==2*len(Q),'State/row census')
mp={int(q):z for q,z in json.loads((D/'legacy_mapping.json').read_text()).items()}
need(set(mp)==Q|{halt} and len(set(mp.values()))==len(mp),'Mapping bijection')
need((mp[0],mp[84],mp[254])==(95,96,254),'Mapping interfaces')
need(U=={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()},'Literal relabeling')
seen={st};todo=[st]
while todo:
    q=todo.pop()
    for b in (0,1):
        z=T[q,b][2]
        if z!=halt and z not in seen:seen.add(z);todo.append(z)
need(seen==Q,'Graph-reachable states')
S,G,M=c.source_graph(D/'sites.json');need(M==r['source_metrics'],'Independent complete source graph')
C=json.loads((D/'cases.json').read_text());expected=[(i,p)for i,s in enumerate(S)for p in ((False,True)if s[1]=='CD'else(False,))]
need([(x['site_index'],x['positive'])for x in C]==expected and len(C)==r['cases']==M['guarded_cases'],'Complete guarded-case coverage')
need(all(type(x['symbolic_steps'])is int and x['symbolic_steps']>0 for x in C),'Symbolic step counts')
need(all(len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0 for x in C),'Unbounded nonnegative positive-duration forms')
need(sum(x['symbolic_steps']for x in C)==r['symbolic_steps'],'Total symbolic rules')
need(min(x['duration'][0]for x in C)==r['minimum_actual_steps'],'Positive duration minimum')
need(r['all_rows_used'] and not r['unused_rows'],'Full row coverage receipt')
need([(b['entry'],b['direction'],b['before'],b['after'])for b in r['blocks']]==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'Four literal finite-list induction schemas')
boot=r['startup'];q,h,ones,_=c.execute(T,0,254,boot['steps'])
need((q,h,sorted(ones))==(84,boot['head'],boot['complete_one_cells']),'Fresh sparse whole-tape startup replay')
need(boot['all_other_cells']==0 and len(boot['physical_registers'])==9 and len(boot['spares'])>=1,'Frame support metadata')
expected_ones={h-1,boot['header']};p=boot['header']+1
for v in boot['physical_registers']+boot['spares']:
    need(type(v)is int and v>=0,'Natural frame words');p+=1;expected_ones.update(range(p,p+v+1));p+=v+1
need(expected_ones==ones and boot['header']-h-64==boot['extra_gap']>=0,'Complete regular frame')
need(boot['logical_seed']==[boot['physical_registers'][j]for j in r['physical_map']],'Logical seed map')
A=dict(status='INDEPENDENT_STORED_RUNTIME_INTEGRITY_SOURCE_COVERAGE_AND_STARTUP_PASS',working_states=len(Q),rows=len(T),cases=len(C),symbolic_steps=r['symbolic_steps'],startup_steps=boot['steps'],table_sha256=sha(D/'candidate.tm'),source_sha256=sha(D/'sites.json'),receipt_sha256=sha(D/'proof.json'),cases_sha256=sha(D/'cases.json'),auditor_sha256=sha(Path(__file__)),source_checker_sha256=sha(Path(c.__file__)),assertions_required=False,scope='Checks literal bijection, total source graph, case coverage, nonnegative positive duration forms, proof provenance and exact complete startup. Stored proof integrity is distinct from the fresh unbounded induction replay that produced the receipt. No changed-calculus adequacy is inferred.')
(D/'independent_runtime_audit.json').write_text(json.dumps(A,indent=2)+'\n');print(json.dumps(A,indent=2))
