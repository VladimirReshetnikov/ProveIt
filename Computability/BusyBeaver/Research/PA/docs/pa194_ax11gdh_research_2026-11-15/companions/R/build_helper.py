#!/usr/bin/env python3
"""Reconstruct a bootstrap-safe, history-recovering 194-state companion.

No compiler, arithmetic-box oracle, network, or nonstandard Python package is
used. The four local cases quantify over both unspecified tape exteriors.
Assertions are certificate obligations, so Python -O is rejected.
"""
from pathlib import Path
import json, hashlib, argparse
HERE=Path(__file__).resolve().parent
START,HALT,HELPER=74,254,3000
NAME='PA194AX11GDHR'
SOURCE_HASHES={'sites.json': '35e015a51d785d7fee861aa793e13b52fc0e543f11c5dfefeb02a4d2c83c479c', 'instructions.json': '46f91e9b210665a1689b12e0d2b88d7c39a84bab66f24c7d38553c2ea82f857d', 'nodes.json': 'f05cf647a40df5d74325e11af2c519bbd8ada8dff377d703a7bfe5f61685e88f', 'grammar.json': '3d6f20c131d8e74cfeb8a5610e04ba230f19a2b61a9b89c737c1f3d3ac8d830a'}
SEED_SHA='d813a3d9f7e9d95407e8343c8a541f267ab1b1016ffe4aa99331eafad639d18f'
PARENT_SHA='2eb51a94fd0c47d5eae802b5d9add156f23f05fa243f6157432cc6c03ffc6221'

def read(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,b]=w,1 if d=='R' else -1,t
    controls={q for q,b in rows}
    assert len(rows)==2*len(controls) and all((q,b) in rows for q in controls for b in (0,1))
    assert {t for w,d,t in rows.values()}-controls=={HALT}
    return rows

def serial(rows):
    return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n'
                   for (q,b),(w,d,t) in sorted(rows.items()))

def alias(q):return 88 if q==301 else q

def guards(parent):
    assert START not in (88,301) and HELPER not in {q for q,b in parent}
    pred=lambda target:[(q,b,w,d) for (q,b),(w,d,t) in sorted(parent.items()) if t==target]
    assert pred(88) and all((w,d)==(1,1) for q,b,w,d in pred(88))
    assert pred(301) and all((w,d)==(0,1) for q,b,w,d in pred(301))
    expected={(88,0):(0,1,122),(88,1):(1,1,103),
              (301,0):(0,1,45),(301,1):(1,1,103),
              (122,0):(0,-1,137),(137,0):(0,1,30),(30,0):(0,1,45)}
    assert all(parent[k]==v for k,v in expected.items())
    assert HALT not in (88,301,HELPER,122,137,30,45,103)
    return {'incoming_88':pred(88),'incoming_301':pred(301),'required_rows':[[*k,*v] for k,v in expected.items()]}

def build(parent):
    child={(q,b):(w,d,alias(t)) for (q,b),(w,d,t) in parent.items() if q!=301}
    child[88,0]=(0,-1,HELPER)
    child[HELPER,0]=(0,1,122)
    child[HELPER,1]=(1,1,HELPER)
    assert len(child)==388 and len({q for q,b in child})==194
    assert child[51,0]==parent[51,0]==(0,1,16)
    assert child[51,1]==parent[51,1]
    return child

def local_cases(parent,child):
    cases=[]
    for q,history in ((88,1),(301,0)):
        for bit in (0,1):
            w,d,t=parent[q,bit]
            desired=(alias(t),d,{-1:history,0:w})
            state,head,tape=alias(q),0,{-1:history,0:bit}
            count=1 if bit else 3 if q==88 else 5
            trace=[[state,head,dict(tape)]]
            for k in range(count):
                assert head in (-1,0) and state!=HALT
                write,move,state=child[state,tape[head]]
                tape[head]=write;head+=move
                trace.append([state,head,dict(tape)])
            assert (state,head,tape)==desired
            cases.append({'parent_state':q,'history_bit':history,'read':bit,
                          'parent_steps':1,'child_steps':count,'trace':trace})
    # Every other old transition commutes with the state map exactly.
    for (q,b),(w,d,t) in parent.items():
        if q not in (88,301):assert child[alias(q),b]==(w,d,alias(t))
    return cases

def startup(parent,child,seed):
    pq=START;ph=0;pt=set();cq=START;ch=0;ct=set();child_clock=0
    uses={'88_read0':0,'301_read0':0}
    for parent_clock in range(seed['steps']):
        assert (cq,ch,ct)==(alias(pq),ph,pt)
        b=int(ph in pt)
        if pq in (88,301):assert int(ph-1 in pt)==(1 if pq==88 else 0)
        count=1
        if b==0 and pq in (88,301):
            count=3 if pq==88 else 5;uses[f'{pq}_read0']+=1
        w,d,pq=parent[pq,b];(pt.add if w else pt.discard)(ph);ph+=d
        for k in range(count):
            assert cq!=HALT
            w,d,cq=child[cq,int(ch in ct)];(ct.add if w else ct.discard)(ch);ch+=d
        child_clock+=count
        assert (cq,ch,ct)==(alias(pq),ph,pt)
    assert (pq,ph,sorted(pt))==(seed['state'],seed['head'],seed['one_cells'])
    assert (cq,ch,sorted(ct))==(seed['state'],seed['head'],seed['one_cells'])
    assert child_clock==seed['steps']+2*uses['88_read0']+4*uses['301_read0']
    return dict(seed,steps=child_clock,parent_steps=seed['steps'],shortcut_inverse_uses=uses,
                whole_prefix_synchronized=True)

def dense(child):
    order=[START];index={START:0}
    for q in order:
        for b in (0,1):
            t=child[q,b][2]
            if t!=HALT and t not in index:index[t]=len(order);order.append(t)
    assert len(order)==194
    return {(index[q],b):(w,d,194 if t==HALT else index[t]) for (q,b),(w,d,t) in child.items()},order+[HALT]

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled; do not use python -O.')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE/NAME);a=ap.parse_args()
    a.output.mkdir(parents=True,exist_ok=True)
    parent_path=HERE/'parent/machine.native.tm';parent=read(parent_path)
    digest=hashlib.sha256(parent_path.read_bytes()).hexdigest()
    if PARENT_SHA:assert digest==PARENT_SHA
    guard=guards(parent);child=build(parent);cases=local_cases(parent,child)
    seed_bytes=(HERE/'parent/startup.json').read_bytes()
    assert hashlib.sha256(seed_bytes).hexdigest()==SEED_SHA
    specification=json.loads(seed_bytes)
    path=json.loads((HERE/'parent/sites.json').read_text())[25][0]
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    expected={-3,46};expected.update(-2+i for i,b in enumerate(path) if int(b))
    pos=47
    for value in physical:
        pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
    assert specification['state']==84 and specification['head']==-2
    assert specification['physical_file']==physical and specification['one_cells']==sorted(expected)
    seed=startup(parent,child,specification)
    table,labels=dense(child)
    files={'machine.native.tm':serial(child),'machine.tm':serial(table),'labels.json':json.dumps(labels)+'\n',
           'guard_certificate.json':json.dumps(guard,indent=2)+'\n','local_cases.json':json.dumps(cases,indent=2)+'\n',
           'startup.json':json.dumps(seed,indent=2)+'\n'}
    for name,data in files.items():(a.output/name).write_text(data)
    for name,expected_hash in SOURCE_HASHES.items():
        raw=(HERE/'parent'/name).read_bytes()
        assert hashlib.sha256(raw).hexdigest()==expected_hash
        (a.output/name).write_bytes(raw)
    receipt={'name':NAME,'parent':'PA194AX11GDH','working_states':194,'rows':388,
             'dense_start':0,'dense_halt':194,'native_start':START,'native_halt':HALT,'helper':HELPER,
             'parent_native_sha256':digest,'parent_seed_sha256':SEED_SHA,'native_sha256':hashlib.sha256(files['machine.native.tm'].encode()).hexdigest(),
             'dense_sha256':hashlib.sha256(files['machine.tm'].encode()).hexdigest(),
             'local_cases':len(cases),'local_durations':[c['child_steps'] for c in cases],
             'all_other_rows_commute':True,'marker_51_unchanged':True,'graph_reachable_states':len(labels)-1,
             'parent_startup_steps':seed['parent_steps'],'startup_steps':seed['steps'],'startup':seed,'source_files_equal_to_parent':True,'source_sha256':SOURCE_HASHES,'whole_prefix_synchronized':True,
             'relative_theorem':'For any complete tape and initial head at control74, parent and child halt equivalently. Parent halting by t implies child halting by5t; child halting by t implies parent halting by t.',
             'arithmetic_scope':'Finite incoming guards and bounded positive stuttering give a written primitive-recursive trace translation formalizable in iPRA. No new Lean endpoint is asserted.'}
    (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
