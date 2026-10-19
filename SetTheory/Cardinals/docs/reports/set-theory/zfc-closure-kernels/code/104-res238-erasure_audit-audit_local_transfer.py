"""Independent generic delayed-erasure theorem side-condition verifier.
No original local certificate is imported. Boundary239 and combined238 are data.
"""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
B=ROOT.parent/'combine/zfc239-research-20261019/candidate239/zfc_boundary239_old.tm'
N=ROOT.parent/'combine/candidate238/zfc_combined238_old.tm'
R=ROOT.parent/'combine/ZFC239_Companion_2026-10-19/reference/zfc240_old.tm'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fail_unless(x,msg):
    if not x:raise ValueError(msg)
def read(p):
    table={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        fail_unless((q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R'),'Bad table')
        table[q,b]=(w,(-1 if d=='L' else 1),z)
    states={q for q,b in table}
    fail_unless(set(table)=={(q,b) for q in states for b in (0,1)},'Incomplete domains')
    fail_unless({z for w,d,z in table.values()}-states=={254},'Wrong halt')
    return table
old=read(B);new=read(N);reference=read(R)
fail_unless(len(old)==478 and len(new)==476,'Wrong state counts')
phi=lambda q:80 if q==169 else q
expected={(q,b):(w,d,phi(z)) for (q,b),(w,d,z) in old.items() if q!=169}
expected[80,0]=(0,-1,106);expected[91,1]=(1,-1,167)
fail_unless(new==expected,'Unexpected changed row')
fail_unless([(q,b) for (q,b),(w,d,z) in old.items() if z==169]==[(147,0)],'Unexpected169 predecessor')
predicate={67:{-1:0},80:{-2:0,-1:1},91:{-3:0,-2:1,-1:1},169:{-1:0}}
incoming=[]
for (q,b),(w,d,z) in old.items():
    if z not in predicate:continue
    known={**predicate.get(q,{}),0:w}
    fail_unless(all(known.get(d+offset)==value for offset,value in predicate[z].items()),'Noninductive structural predicate')
    incoming.append({'row':[q,b],'transition':[w,d,z]})
fail_unless(95 not in predicate,'Initial predicate unsupported')
specs=[(80,{-1:1,0:0},1,5),(80,{0:1},1,1),(169,{-1:0,0:0},1,3),(169,{-1:0,0:1,1:1},1,5),(91,{0:0},1,1),(91,{-3:0,-2:1,-1:1,0:1},3,11)]
support=set()
def run(table,q,facts,steps):
    tape=dict(facts);head=0;trace=[]
    for tick in range(steps):
        fail_unless(q!=254,'Premature halt')
        fail_unless(head in tape,'Unconstrained exterior read')
        b=tape[head];w,d,z=table[q,b];support.add((q,b))
        trace.append({'q':q,'h':head,'read':b,'write':w,'move':d,'next':z})
        tape[head]=w;head+=d;q=z
    return q,head,tape,trace
proofs=[]
for q,facts,oldsteps,newsteps in specs:
    a=run(old,q,facts,oldsteps);b=run(new,phi(q),facts,newsteps)
    fail_unless(phi(a[0])==b[0] and a[1]==b[1],'Control or head mismatch')
    for pos in a[2].keys()|b[2].keys():
        original=('arbitrary_initial_bit',pos)
        fail_unless(a[2].get(pos,original)==b[2].get(pos,original),'Whole tape mismatch')
    fail_unless(oldsteps>0 and newsteps>0 and oldsteps<=newsteps<=5*oldsteps,'Nonpositive or bad ratio')
    proofs.append({'state':q,'assumptions':facts,'old_steps':oldsteps,'new_steps':newsteps,'endpoint':[a[0],a[1]],'old_trace':a[3],'new_trace':b[3]})
# Local proof support survives all boundary source/control changes literally.
fail_unless(all(old[key]==reference[key] for key in support),'Boundary changes local theorem support')
result={'status':'PARAMETRIC_DELAYED_ERASURE_TRANSFER_SIDE_CONDITIONS_PASS','baseline_sha256':digest(B),'candidate_sha256':digest(N),'reference240_sha256':digest(R),'verifier_sha256':digest(Path(__file__)),'old_working_states':239,'new_working_states':238,'exact_edit_set':[[80,0],[91,1],[147,0]],'deleted':169,'structural_invariant':predicate,'incoming_rows':incoming,'local_support_rows':sorted(support),'local_support_unchanged_from_original':True,'cases':proofs,'initial_state':95,'halt':254,'semantic_premise':'Along the boundary239 blank run, q169/read1 implies next cell1; independently checked in boundary_guard.json.','theorem':'Any complete binary old table with these local identities, incoming invariants and reachable guard is halting-equivalent from the common initial configuration to the exact patched table. Other transition rows are unrestricted subject to invariant preservation and the guard.'}
(ROOT/'local_transfer.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','local_support_rows')},indent=2))
