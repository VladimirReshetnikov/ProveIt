#!/usr/bin/env python3
"""Independent literal audit of the even195HX research construction.

No construction compiler, macro simulator, or arithmetic-box oracle is
imported. List traversal lemmas are rederived from the literal transitions.
Two separate source resolvers must agree. Python 3.10+, standard library,
without -O. This is an executable universal certificate, not a newly
kernel-checked consistency theorem.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source

PHY = (6,2,0,4,3,8,7,5,1)
STATES, START, HALT, SOURCE_ENTRY = 195,74,254,84
SEED_PC, SEED_STEPS = 40,44094
SEED_LOGICAL = [4,0,0,0,0,0,0,0,1]
FINAL_LOGICAL = [4,0,0,0,0,0,0,0,0]
SPARES = 29
sym.HEADER_BASE = 48

def sha(data): return hashlib.sha256(data).hexdigest()
def dump(path,data):
    path.write_text(json.dumps(data,indent=2,default=lambda x:sorted(x) if isinstance(x,set) else str(x))+'\n')

def read_table(path):
    rows={}
    for line in path.read_text().splitlines():
        fields=line.split(); assert len(fields)==5
        q,b,w,d,t=fields; q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,b]=(w,d,t)
    return rows

def check(inputs,outdir):
    assert __debug__ and not sys.flags.optimize
    outdir.mkdir(parents=True,exist_ok=True)
    rows=read_table(inputs/'even195HX.native.tm')
    controls={q for q,b in rows}
    assert len(controls)==STATES and len(rows)==2*STATES
    assert set(rows)=={(q,b)for q in controls for b in (0,1)}
    assert {t for w,d,t in rows.values()}-controls=={HALT}
    assert 3000 in controls and HALT not in controls
    reachable={START};todo=[START]
    for q in todo:
        for b in (0,1):
            t=rows[q,b][2]
            if t!=HALT and t not in reachable:reachable.add(t);todo.append(t)
    assert reachable==controls
    labels=json.loads((inputs/'even195HX.labels.json').read_text())
    assert len(labels)==len(set(labels))==STATES+1
    assert labels[0]==START and labels[-1]==HALT and set(labels[:-1])==controls
    dense=read_table(inputs/'even195HX.tm')
    assert set(dense)=={(q,b)for q in range(STATES)for b in (0,1)}
    assert all(0<=t<=STATES for w,d,t in dense.values())
    assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==rows

    sites=json.loads((inputs/'source.sites.json').read_text())
    assert len(sites)==3674
    names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,names[op],arg]for p,op,arg in sites]
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert instructions==json.loads((inputs/'source.instructions.json').read_text())

    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in controls|{HALT}:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in controls|{HALT}})==STATES+1
    assert mapping[SOURCE_ENTRY]==96 and mapping[3000]==13000
    table={(mapping[q],b):(w,1 if d=='R'else-1,mapping[t])
           for(q,b),(w,d,t)in rows.items()}
    runtime.PHY=PHY
    lemmas,blocks=sym.prove_blocks(table)
    assert len(blocks)==4
    contracts=[];total=maximum=0
    for i,site in enumerate(mapped):
        for positive in ([False,True] if site[1]=='CD' else [False]):
            result=sym.case(table,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append(dict(site=i,positive=positive,**result))
        if (i+1)%1000==0:print('checked',i+1,'source sites',flush=True)
    assert len(contracts)==4781
    minimum=min(x['duration'][0]for x in contracts)
    assert minimum>0

    # Independent dense-array replay, with complete finite-support equality.
    tape=bytearray(20000);head=10000;q=START
    for step in range(SEED_STEPS):
        assert q!=HALT and 0<=head<len(tape)
        w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d=='R'else-1
    assert (q,head)==(SOURCE_ENTRY,9998)
    physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=SEED_LOGICAL[i]
    assert physical==[0,1,0,0,0,0,4,0,0]
    p=mapped[SEED_PC][0]
    frame=bytearray([1]+[int(b)for b in p]+[0]*(48-len(p))+[1])
    for value in physical+[1]*SPARES:frame.extend([0]+[1]*(value+1))
    expected=bytearray(len(tape));expected[head-1:head-1+len(frame)]=frame
    assert tape==expected
    seed=dict(status='PASS',steps=SEED_STEPS,state=q,head=head-10000,
              source_pc=SEED_PC,header_gap=0,logical_registers=SEED_LOGICAL,
              physical_registers=physical,spare_values=[1]*SPARES,
              complete_tape_equality=True,
              one_cells=[i-10000 for i,v in enumerate(tape)if v])

    # Execute the independently resolved source graph, not the builder trace.
    registers=list(SEED_LOGICAL);pc=SEED_PC;trace=[]
    for step in range(48):
        assert not(pc==25 and registers==FINAL_LOGICAL)
        ins=instructions[pc]
        trace.append(dict(pc=pc,registers=list(registers),instruction=ins))
        if ins[0]=='inc':
            _,r,next_pc=ins;registers[r]+=1
        elif ins[0]=='dec':
            _,r,zero,positive=ins
            if registers[r]:registers[r]-=1;next_pc=positive
            else:next_pc=zero
        elif ins[0]=='jump':next_pc=ins[1]
        else:raise AssertionError('Unexpected source halt in finite bridge')
        pc=next_pc
    assert pc==25 and registers==FINAL_LOGICAL
    trace.append(dict(pc=pc,registers=list(registers)))
    assert trace==json.loads((inputs/'seed_bridge.json').read_text())
    bridge=dict(status='PASS',steps=48,start_pc=SEED_PC,final_pc=25,
                start_registers=SEED_LOGICAL,final_registers=FINAL_LOGICAL,
                instructions_from_independent_resolvers=True,trace=trace)

    raw=json.dumps(contracts,separators=(',',':'),default=lambda x:sorted(x)if isinstance(x,set)else str(x)).encode()
    (outdir/'contracts.json').write_bytes(raw)
    dump(outdir/'list_lemmas.json',blocks)
    dump(outdir/'blank_seed.json',seed)
    dump(outdir/'source_bridge.json',bridge)
    dump(outdir/'resolved_instructions.json',instructions)
    receipt=dict(family='even195HX',status='PASS',working_states=STATES,rows=len(rows),
                 graph_reachable_states=len(reachable),source_sites=len(mapped),
                 source_outcomes=len(contracts),logical_to_physical=list(PHY),
                 symbolic_steps=total,maximum_symbolic_steps=maximum,
                 minimum_positive_duration_constant=minimum,
                 list_lemmas_from_literal_table=4,box_oracles=False,
                 compiler_imported=False,independent_source_resolvers_agree=True,
                 dense_native_conjugacy=True,whole_blank_startup=True,
                 startup_steps=SEED_STEPS,seed_source_pc=SEED_PC,source_bridge_steps=48,
                 clean_source_pc=25,clean_candidate=4,
                 dense_sha256=sha((inputs/'even195HX.tm').read_bytes()),
                 native_sha256=sha((inputs/'even195HX.native.tm').read_bytes()),
                 contracts_sha256=sha(raw),kernel_checked=False,
                 scope='Independent literal physical/source certificate over arbitrary natural primary registers, both decrement branches, an affine header gap and an arbitrary nonempty finite spare list. Whole blank initialization and finite clean-entry bridge checked. Enumeration completeness and logical PA calibration are separate ordinary mathematical arguments.')
    dump(outdir/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs',type=Path,default=HERE/'inputs')
    parser.add_argument('--output',type=Path,default=HERE/'recorded')
    args=parser.parse_args();check(args.inputs,args.output)
