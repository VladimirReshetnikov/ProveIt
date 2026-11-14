#!/usr/bin/env python3
"""Independent whole-tape symbolic audit of the exact 195S/195C tables.

All natural register values and arbitrary finite nonempty spare lists are
covered. No arithmetic register-box oracle or bounded numeric sampling is used.
Requires Python 3 with assertions enabled; no external packages are needed.
"""
from pathlib import Path
import argparse,hashlib,json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as s
import source_language as source

EXPECTED={
    '195S':(3673,4780,58154,'dcad583f1731bc41117be63bf8f4f7e69ab58409c18bcb56cf906337a996afae'),
    '195C':(3649,4749,57922,'8f34d9e5cc2e64ecc49bbc8581dc29b2ac0a84ad9187c4dd8b7597588ef22ea3'),
}

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def read_table(p,halt):
    table={}
    for line in p.read_text().splitlines():
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in table and q!=halt
        table[q,b]=(w,1 if d=='R' else -1,t)
    states={q for q,b in table};assert len(states)==195
    assert set(table)=={(q,b)for q in states for b in (0,1)}
    assert all(t in states or t==halt for w,d,t in table.values())
    return table

def check(family):
    inp=HERE/'inputs'/family;out=HERE/'results'/family;out.mkdir(parents=True,exist_ok=True)
    n,want_cases,startup_steps,want_sha=EXPECTED[family]
    assert digest(inp/'machine.native.tm')==want_sha
    table=read_table(inp/'machine.native.tm',254)
    dense=read_table(inp/'machine.dense.tm',195)
    labels=json.loads((inp/'dense_to_native.json').read_text())
    assert len(labels)==196 and labels[0]==74 and labels[-1]==254 and len(set(labels))==196
    assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==table
    reached=[74];seen={74}
    for q in reached:
        for b in (0,1):
            t=table[q,b][2]
            if t!=254 and t not in seen:seen.add(t);reached.append(t)
    assert reached+[254]==labels
    sites=json.loads((inp/'source.sites.json').read_text());assert len(sites)==n
    opcode={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    sites=[[p,opcode[op],arg]for p,op,arg in sites]
    graph,_=source.graph_arithmetic(sites)
    assert graph==source.graph_intervals(sites)
    opname={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[opname[effect[0]]]+effect[1:]+targets for effect,targets in graph]
    assert instructions==json.loads((inp/'source.instructions.json').read_text())
    assert max(len(p)for p,op,arg in sites)<=48

    # Relabeling makes the reference engine's four generic list-sweep entry
    # names applicable. Every list lemma is rederived from the new table.
    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in labels:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in labels})==196
    symbolic_table={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in table.items()}
    assert mapping[84]==96 and mapping[254]==254
    s.HEADER_BASE=48
    lemmas,blocks=s.prove_blocks(symbolic_table)
    summaries=[];all_rows=set();kinds={};total=0;max_steps=0
    for i,site in enumerate(sites):
        for positive in ([False,True]if site[1]=='CD'else[False]):
            result=s.case(symbolic_table,lemmas,site,positive)
            all_rows.update(result['rows'])
            for kind,count in result['kinds'].items():kinds[kind]=kinds.get(kind,0)+count
            total+=result['symbolic_steps'];max_steps=max(max_steps,result['symbolic_steps'])
            summaries.append(dict(site=i,positive_decrement=positive,symbolic_steps=result['symbolic_steps'],duration=result['duration'],motion=result['motion'],kinds=result['kinds']))
        if (i+1)%500==0:print(family,'sites',i+1,'contracts',len(summaries),flush=True)
    assert len(summaries)==want_cases

    # Exact blank run: compare the whole finite-support tape, state and head.
    tape=set();q=74;head=0
    for step in range(startup_steps):
        assert q!=254,('early blank halt',step)
        w,d,q=table[q,int(head in tape)]
        (tape.add if w else tape.discard)(head);head+=d
    expected_head=-2
    expected={expected_head-1,expected_head+48}|{expected_head+i for i,b in enumerate(sites[25][0])if b=='1'}
    pos=expected_head+49
    for value in [0,0,0,0,0,0,2,0,0]+[1]*26:
        expected.update(range(pos+1,pos+value+2));pos+=value+2
    assert q==84 and head==expected_head and tape==expected
    (out/'contracts.json').write_text(json.dumps(summaries,separators=(',',':'))+'\n')
    (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    seed=dict(steps=startup_steps,state=q,head=head,ones=sorted(tape),site=25,gap=48,
              logical_registers=[2,0,0,0,0,0,0,0,0],spare_values=[1]*26)
    (out/'blank_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    receipt=dict(family=family,status='PASS',working_states=195,transition_rows=390,
       graph_reachable_working_states=len(reached),dense_conjugacy_exact=True,
       native_table_sha256=want_sha,dense_table_sha256=digest(inp/'machine.dense.tm'),
       source_sites=n,source_sha256=digest(inp/'source.sites.json'),
       independently_resolved_source_graph_equal=True,header_base=48,
       universal_source_outcomes=len(summaries),symbolic_steps=total,max_symbolic_steps=max_steps,
       event_counts=kinds,source_register_values='arbitrary natural values; both decrement outcomes',
       spare_list='arbitrary finite nonempty list of arbitrary natural values',
       list_lemmas_rederived_from_literal_table=len(blocks),arithmetic_box_oracles=False,
       blank_startup_steps=startup_steps,complete_blank_seed_equal=True,
       contracts_sha256=digest(out/'contracts.json'),list_lemmas_sha256=digest(out/'list_lemmas.json'),
       blank_seed_sha256=digest(out/'blank_seed.json'),
       kernel_checked=False,scope='universal literal tape simulation and exact blank seed; logical calibration is a separate proof')
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('family',choices=['195S','195C','both'],nargs='?',default='both')
    args=ap.parse_args()
    for family in (['195S','195C']if args.family=='both'else[args.family]):check(family)
