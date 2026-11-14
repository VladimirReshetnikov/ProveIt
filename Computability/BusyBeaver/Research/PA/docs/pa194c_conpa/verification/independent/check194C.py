#!/usr/bin/env python3
"""Independent universal literal-tape and corpus-novelty checks.

Only Python's standard library is required. This checker imports no machine
compiler, allocator, or arithmetic-box oracle. Four generic list-sweep lemmas
are rederived from each supplied literal table. The inherited symbolic engine
is credited in reference/README.md. This is executable mathematical evidence,
not a newly exported Lean/Rocq theorem or an end-to-end PA proof compiler.
"""
from pathlib import Path
import argparse,collections,hashlib,json,sys,tempfile

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[1]
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48
if not __debug__:
    raise RuntimeError('Use Python without -O or PYTHONOPTIMIZE.')

def sha(data): return hashlib.sha256(data).hexdigest()
def parse(path,expected_count=195):
    rows={}
    for line in path.read_text().splitlines():
        line=line.strip()
        if not line or line.startswith(('#','//',';')):continue
        q,b,w,d,t=line.split(); q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    assert len(states)==expected_count and set(rows)=={(q,b) for q in states for b in (0,1)}
    halts={t for w,d,t in rows.values()}-states
    assert len(halts)==1
    return rows,states,next(iter(halts))

def rooted(rows,states,halt,root):
    labels={root:0};todo=[root];out=[]
    for q in todo:
        rr=[]
        for bit in (0,1):
            w,d,t=rows[q,bit]
            if t==halt: k=-1
            else:
                if t not in labels: labels[t]=len(todo);todo.append(t)
                k=labels[t]
            rr.append([w,d,k])
        out.append(rr)
    if len(todo)!=len(states): return None
    return json.dumps(out,separators=(',',':')).encode()

def unrooted(rows,states,halt):
    forms=[x for q in sorted(states) if (x:=rooted(rows,states,halt,q)) is not None]
    assert forms,'No root reaches the complete working graph.'
    return sha(min(forms)),len(forms)

def bisimulation_classes(rows,states,halt):
    partition={q:0 for q in states};partition[halt]=-1
    while True:
        sig={q:tuple((w,d,partition[t]) for w,d,t in (rows[q,0],rows[q,1])) for q in states}
        unique={s:i for i,s in enumerate(sorted(set(sig.values())))}
        new={q:unique[sig[q]] for q in states};new[halt]=-1
        if all((partition[a]==partition[b])==(new[a]==new[b]) for a in states for b in states):
            return len(unique)
        partition=new

def check(job,old,out):
    family=job['family'];n=job.get('working_states',195);directory=out/family;directory.mkdir(parents=True,exist_ok=True)
    inp=lambda k: PACKAGE/job[k]
    native=inp('native');dense_path=inp('dense');site_path=inp('sites');ins_path=inp('instructions')
    assert sha(native.read_bytes())==job['native_sha256']
    assert sha(dense_path.read_bytes())==job['dense_sha256']
    rows,states,halt=parse(native,n);assert halt==254
    dense,dense_states,dense_halt=parse(dense_path,n)
    assert dense_states==set(range(n)) and dense_halt==n
    labels=json.loads(inp('labels').read_text())
    assert len(labels)==n+1 and labels[0]==74 and labels[-1]==254 and len(set(labels))==n+1
    assert {(labels[q],b):(w,d,labels[t]) for (q,b),(w,d,t) in dense.items()}==rows
    graph_hash,root_count=unrooted(rows,states,halt)
    same_size=old
    assert graph_hash not in {h for h,_ in old},'Existing graph, not a new physical design.'
    # Global left/right reflection is a trivial tape symmetry. Exclude it too.
    signature=collections.Counter((w,d) for w,d,t in rows.values())
    for old_hash,(old_rows,old_states,old_halt) in old:
        reflected={(q,b):(w,'R' if d=='L' else 'L',t) for(q,b),(w,d,t) in old_rows.items()}
        if signature==collections.Counter((w,d) for w,d,t in reflected.values()):
            assert graph_hash!=unrooted(reflected,old_states,old_halt)[0]

    physical=tuple(job['physical_map']);assert sorted(physical)==list(range(9))
    sites=json.loads(site_path.read_text())
    opcode={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,opcode[op],arg] for p,op,arg in sites]
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert instructions==json.loads(ins_path.read_text())
    assert instructions==json.loads(inp('reference_instructions').read_text())
    assert len(sites)==job['source_sites'] and max(len(p) for p,op,arg in sites)<=48

    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in states|{halt}:mapping.setdefault(q,q+10000)
    assert len({mapping[q] for q in states|{halt}})==n+1
    assert mapping[84]==96 and mapping[254]==254
    table={(mapping[q],b):(w,1 if d=='R' else -1,mapping[t]) for(q,b),(w,d,t) in rows.items()}
    runtime.PHY=physical
    lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
    contracts=[];total=0;maximum=0
    for i,site in enumerate(mapped):
        for positive in ([False,True] if site[1]=='CD' else [False]):
            result=sym.case(table,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append({'site':i,'positive':positive,'duration':result['duration'],
                              'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
        if (i+1)%1000==0:print(family,'checked sites',i+1,flush=True)
    assert len(contracts)==job['source_contracts']

    # Bytearray startup simulation is separate from the builder's set simulator.
    tape=bytearray(20000);origin=10000;head=origin;q=74
    for step in range(job['startup_steps']):
        assert q!=254 and 0<=head<len(tape),'Early halt or startup tape bound exceeded.'
        w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d=='R' else -1
    assert q==84 and head-origin==-2
    path=sites[25][0]
    frame=bytearray([1]+[int(b) for b in path]+[0]*(48-len(path))+[1])
    logical=[2]+[0]*8;values=[None]*9
    for i,j in enumerate(physical):values[j]=logical[i]
    for value in values+[1]*26:frame.extend([0]+[1]*(value+1))
    expected=bytearray(len(tape));first=head-1;expected[first:first+len(frame)]=frame
    assert tape==expected,'Whole startup tape differs.'
    encoded=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (directory/'contracts.json').write_bytes(encoded)
    (directory/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    seed={'state':q,'head':head-origin,'ones':[i-origin for i,b in enumerate(tape) if b],
          'source_site':25,'source_path':path,'gap':48,'logical_registers':logical,
          'physical_registers':values,'spare_values':[1]*26}
    (directory/'blank_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    receipt={
        'family':family,'status':'PASS','working_states':n,'transition_rows':2*n,
        'native_sha256':sha(native.read_bytes()),'dense_sha256':sha(dense_path.read_bytes()),
        'dense_native_conjugacy_exact':True,'root_free_graph_sha256':graph_hash,
        'pointed_graph_sha256':sha(rooted(rows,states,halt,74)),
        'different_from_primary_PA194_and_AD':True,'same_size_compared_graphs':len(same_size),'not_a_global_tape_reflection':True,
        'full_reaching_roots':root_count,'ordinary_action_bisimulation_classes':bisimulation_classes(rows,states,halt),
        'physical_register_map':physical,'source_sites':len(sites),'source_contracts':len(contracts),
        'independent_cfg_resolvers_agree':True,'logical_source_cfg_equal_to_reference':True,
        'source_reference':job['reference_instructions'],'source_reference_sha256':sha(inp('reference_instructions').read_bytes()),
        'symbolic_steps':total,'maximum_symbolic_steps':maximum,
        'minimum_positive_duration_constant':min(x['duration'][0] for x in contracts),
        'list_lemmas_rederived_from_literal_table':4,'arithmetic_box_oracles':False,
        'register_scope':'nine independent arbitrary natural values; both decrement outcomes',
        'spare_scope':'arbitrary finite nonempty list of arbitrary natural values',
        'startup_steps':job['startup_steps'],'whole_blank_tape_equal':True,
        'contracts_sha256':sha(encoded),'kernel_checked':False,
        'scope':'universal literal source-frame simulation, dense conjugacy, exact blank startup, comparison against the two published positive194 graphs; logical calibration is separate'
    }
    (directory/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

def main():
    out=HERE/'recorded_C'
    out.mkdir(exist_ok=True)
    old=[]
    for name in ['pa194.native.tm','pa194_AD.native.tm']:
        rows,states,halt=parse(PACKAGE/'construction/tables'/name,194)
        old.append((unrooted(rows,states,halt)[0],(rows,states,halt)))
    root='construction/rebuilt_194C/'
    job={'family':'PA194C','working_states':194,
         'native':root+'pa194C.native.tm','dense':root+'pa194C.tm',
         'native_sha256':'b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c',
         'dense_sha256':'d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b',
         'labels':root+'pa194C.labels.json','sites':root+'pa194C.sites.json',
         'instructions':root+'pa194C.instructions.json',
         'reference_instructions':'verification/independent/reference_inputs/195C.instructions.json',
         'source_sites':3649,'source_contracts':4749,'startup_steps':57922,
         'physical_map':[6,2,0,4,3,7,8,5,1]}
    check(job,old,out)

if __name__=='__main__': main()
