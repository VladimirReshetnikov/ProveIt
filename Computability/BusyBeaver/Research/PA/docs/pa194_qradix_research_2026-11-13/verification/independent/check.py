#!/usr/bin/env python3
"""Independent literal tape verification for the PA194Q5/Q6 construction.

Imports no builder or arithmetic-box oracle. The four list-sweep lemmas
are reconstructed from literal rows by the retained symbolic induction engine.
This is executable mathematical evidence, not a proof-assistant kernel.
"""
from pathlib import Path
import argparse, hashlib, json, sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O.')
sym.HEADER_BASE=48
PHY=(6,2,0,4,3,7,8,5,1)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in rows and b in(0,1)and w in(0,1)and d in('L','R')
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    assert len(states)==194 and len(rows)==388
    assert set(rows)=={(q,b)for q in states for b in(0,1)}
    return rows,states

def check(path,output):
    native=path/'native.tm'
    if not native.exists():native=path/'machine.native.tm'
    rows,states=parse(native)
    assert {t for w,d,t in rows.values()}-states=={254}
    dense,dense_states=parse(path/'machine.tm')
    assert dense_states==set(range(194))
    assert {t for w,d,t in dense.values()}-dense_states=={194}
    labels=json.loads((path/'labels.json').read_text())
    assert len(labels)==len(set(labels))==195 and labels[0]==74 and labels[-1]==254
    assert set(labels[:-1])==states
    assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==rows
    reachable={74};todo=[74]
    for q in todo:
        for b in(0,1):
            t=rows[q,b][2]
            if t!=254 and t not in reachable:reachable.add(t);todo.append(t)
    assert reachable==states
    mapped=[]
    names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    for p,op,arg in json.loads((path/'sites.json').read_text()):
        if not isinstance(p,str):p=''.join(map(str,p))
        mapped.append([p,names[op],arg])
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    effect_names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[effect_names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert instructions==json.loads((path/'instructions.json').read_text())
    # A bijective label translation identifies the generic list-lemma entries.
    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in states|{254}})==195 and mapping[84]==96 and mapping[254]==254
    table={(mapping[q],b):(w,1 if d=='R'else-1,mapping[t])for(q,b),(w,d,t)in rows.items()}
    runtime.PHY=PHY
    lemmas,blocks=sym.prove_blocks(table)
    assert len(blocks)==4
    contracts=[];total=maximum=0
    for i,site in enumerate(mapped):
        for positive in([False,True]if site[1]=='CD'else[False]):
            result=sym.case(table,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append(dict(site=i,positive=positive,**result))
        if(i+1)%1000==0:print(path.name,'checked',i+1,flush=True)
    # Exact whole finite-support tape. No fixed window or sampled startup test.
    q=74;head=0;ones=set();steps=58320
    for step in range(steps):
        assert q!=254
        w,d,q=rows[q,int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head+=1 if d=='R'else-1
    assert(q,head)==(84,-2)
    logical=[2]+[0]*8;physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    address=mapped[25][0]
    expected={head-1,head+48}
    expected.update(head+i for i,b in enumerate(address)if b=='1')
    position=head+49
    for v in physical+[1]*26:
        position+=1;expected.update(range(position,position+v+1));position+=v+1
    assert ones==expected
    outdir=output/path.name;outdir.mkdir(parents=True,exist_ok=True)
    serialize=lambda x:sorted(x)if isinstance(x,set)else str(x)
    raw=json.dumps(contracts,separators=(',',':'),default=serialize).encode()
    (outdir/'contracts.json').write_bytes(raw)
    (outdir/'list_lemmas.json').write_text(json.dumps(blocks,indent=2,default=serialize)+'\n')
    (outdir/'startup.json').write_text(json.dumps({'steps':steps,'state':q,'head':head,'one_cells':sorted(ones)},indent=2)+'\n')
    receipt=dict(family=path.name,status='PASS',states=194,rows=388,source_sites=len(mapped),source_outcomes=len(contracts),
        symbolic_steps=total,maximum_symbolic_steps=maximum,minimum_positive_duration_constant=min(x['duration'][0]for x in contracts),
        list_lemmas_from_literal_table=4,box_oracles=False,independent_source_resolvers_agree=True,dense_native_conjugacy=True,
        all_states_graph_reachable=True,whole_blank_startup=True,startup_steps=steps,
        dense_sha256=sha(path/'machine.tm'),native_sha256=sha(native),contracts_sha256=hashlib.sha256(raw).hexdigest(),
        scope='Nine arbitrary natural primary registers, both decrement branches, arbitrary nonempty finite spare list, arbitrary affine nonnegative gap, complete blank exteriors. Executable symbolic induction, not an end-to-end Lean or Rocq PA proof.')
    (outdir/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machines',nargs='+',type=Path)
    parser.add_argument('--output',type=Path,default=HERE/'results')
    args=parser.parse_args()
    for p in args.machines:check(p,args.output)
