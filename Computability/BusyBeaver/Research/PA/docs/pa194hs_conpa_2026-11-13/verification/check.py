#!/usr/bin/env python3
"""Independent literal-tape check of the hybrid 194-state candidates.

The symbolic engine and two source-graph resolvers are inherited unchanged,
with their original licenses under reference/. No compiler or register-box
oracle is imported. This is executable mathematical evidence, not a newly
kernel-checked PA, Lean, or Rocq proof.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source

def sha(b):return hashlib.sha256(b).hexdigest()
def read_table(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith(('#','//',';')):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in rows
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    assert len(states)==194 and set(rows)=={(q,b) for q in states for b in (0,1)}
    halts={t for w,d,t in rows.values()}-states
    assert len(halts)==1
    return rows,states,next(iter(halts))

def main():
    assert __debug__ and not sys.flags.optimize,'Run with assertions enabled.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('machine',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();machine=args.machine;out=args.output or machine/'independent';out.mkdir(parents=True,exist_ok=True)
    construction=json.loads((machine/'construction_receipt.json').read_text())
    seed_steps=construction['startup']['steps']
    native,states,halt=read_table(machine/'machine.native.tm');assert halt==254
    dense,dense_states,dense_halt=read_table(machine/'machine.tm')
    assert dense_states==set(range(194)) and dense_halt==194
    labels=[74];seen={74}
    for q in labels:
        for b in (0,1):
            t=native[q,b][2]
            if t!=halt and t not in seen:seen.add(t);labels.append(t)
    assert seen==states
    labels.append(halt)
    assert {(labels[q],b):(w,d,labels[t]) for (q,b),(w,d,t) in dense.items()}==native
    (out/'labels.json').write_text(json.dumps(labels)+'\n')

    raw=json.loads((machine/'source.json').read_text())
    sites=[[''.join(map(str,p)),op,arg] for p,op,arg in raw['sites']]
    opcode={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,opcode[op],arg] for p,op,arg in sites]
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert instructions==raw['instructions']
    assert len(sites)==construction['source_sites'] and max(len(p) for p,op,arg in sites)<=48
    (out/'sites.json').write_text(json.dumps(sites)+'\n')
    (out/'instructions.json').write_text(json.dumps(instructions)+'\n')

    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in states|{halt}:mapping.setdefault(q,q+10000)
    assert len({mapping[q] for q in states|{halt}})==195
    assert mapping[84]==96 and mapping[254]==254
    table={(mapping[q],b):(w,1 if d=='R' else -1,mapping[t]) for (q,b),(w,d,t) in native.items()}
    runtime.PHY=(6,2,0,4,3,7,8,5,1);sym.HEADER_BASE=48
    lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
    contracts=[];total=0;maximum=0
    for i,site in enumerate(mapped):
        for positive in ([False,True] if site[1]=='CD' else [False]):
            result=sym.case(table,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append(dict(site=i,positive=positive,duration=result['duration'],
                                  motion=result['motion'],symbolic_steps=result['symbolic_steps']))
        if (i+1)%1000==0:print('Checked',i+1,'primitive sites',flush=True)
    assert len(contracts)==construction['source_outcomes']

    # Independent bytearray execution and comparison of the entire blank seed.
    tape=bytearray(20000);origin=10000;head=origin;q=74
    for step in range(seed_steps):
        assert q!=254 and 0<=head<len(tape)
        w,d,q=native[q,tape[head]];tape[head]=w;head+=1 if d=='R' else -1
    assert q==84 and head-origin==-2
    pc=sites[25][0]
    frame=bytearray([1]+[int(b) for b in pc]+[0]*(48-len(pc))+[1])
    logical=[2]+[0]*8;values=[None]*9
    for i,j in enumerate(runtime.PHY):values[j]=logical[i]
    for value in values+[1]*26:frame.extend([0]+[1]*(value+1))
    expected=bytearray(len(tape));first=head-1;expected[first:first+len(frame)]=frame
    assert tape==expected,'Whole startup tape differs.'
    seed=dict(state=q,head=head-origin,ones=[i-origin for i,b in enumerate(tape) if b],
              source_site=25,source_path=pc,gap=48,logical_registers=logical,
              physical_registers=values,spare_values=[1]*26)
    encoded=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (out/'contracts.json').write_bytes(encoded)
    (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    (out/'blank_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    receipt=dict(status='PASS',family=construction['family'],working_states=194,transition_rows=388,
        dense_sha256=sha((machine/'machine.tm').read_bytes()),native_sha256=sha((machine/'machine.native.tm').read_bytes()),
        source_sha256=sha((machine/'source.json').read_bytes()),dense_native_conjugacy_exact=True,
        all_working_states_graph_reachable=True,source_sites=len(sites),source_contracts=len(contracts),
        independent_cfg_resolvers_agree=True,declared_instruction_graph_exact=True,
        symbolic_steps=total,maximum_symbolic_steps=maximum,
        minimum_positive_duration_constant=min(x['duration'][0] for x in contracts),
        list_lemmas_rederived_from_actual_rows=4,arithmetic_box_oracles=False,
        physical_register_map=runtime.PHY,
        register_scope='nine arbitrary natural values; both decrement outcomes',
        spare_scope='arbitrary finite nonempty list of arbitrary natural values',
        gap_scope='48+n for arbitrary natural n',
        startup_steps=seed_steps,whole_blank_tape_equal=True,
        contracts_sha256=sha(encoded),kernel_checked=False,
        scope='literal-table universal source-frame simulation and exact startup; command and logical calibration remain separate')
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
