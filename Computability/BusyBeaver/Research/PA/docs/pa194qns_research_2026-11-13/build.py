#!/usr/bin/env python3
"""Reconstruct the exact PA194QNS and PA194QS machines.

Only Python's standard library is required. The inherited construction
executor uses fixed register-block contracts; verification/check_literal.py
provides a separate literal-tape audit without those block oracles.
Assertions must be enabled. No files outside the selected output are changed.
"""
from pathlib import Path
import argparse, hashlib, json, sys, tempfile

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import compiler as c
BASE_NODES=c.raw_nodes
START,HALT=74,254
EXPECTED={
    'PA194QNS':('7eb36aea69e5de46cc47fa7aab0191f191657ab500dafb808dc3c394640591b8',3651,4751,1512246),
    'PA194QS':('fcfa7e87fcec2117ea21a84312dc8bb15841fb3c8cfd267ed40946a5ca4b1407',3670,4776,1518350),
}

def sha(data):return hashlib.sha256(data).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for (q,b),(w,d,n) in sorted(rows.items()))
def read_table(path):
    out={}
    for line in path.read_text().splitlines():
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in out and b in (0,1) and w in (0,1) and d in ('L','R')
        out[q,b]=(w,d=='R',n)
    return out

def nodes(nopush,symmetric):
    out=BASE_NODES()
    assert out['node163']==('node6','node55')
    assert out['node168']==('node37','node57')
    assert out['node171']==('node170','node23')
    if nopush:out['node163']=('node6','node54')
    if symmetric:
        out['node168']=('node37','node56')
        out['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    return out

def fold(raw,folds):
    alias={a:b for a,b,_ in folds}
    acts={b:ab for a,b,ab in folds}
    assert len({q for a,b,_ in folds for q in (a,b)})==2*len(folds)
    rows={}
    for (q,bit),action in raw.items():
        if q in alias:continue
        w,d,n=acts[q][bit] if q in acts else action
        rows[q,bit]=(w,bool(d),alias.get(n,n))
    return rows,alias

def check_folds(raw,rows,folds,alias):
    incoming={}
    for (q,bit),(w,d,n) in raw.items():incoming.setdefault(n,[]).append([q,bit,w,d,n])
    cases=[]
    for a,b,_ in folds:
        assert START not in (a,b)
        for old,history in ((a,0),(b,1)):
            assert incoming[old]
            assert all((w,d)==(history,True) for q,bit,w,d,n in incoming[old])
            for bit in (0,1):
                w,d,n=raw[old,bit]
                goal=(alias.get(n,n),1 if d else -1,{-1:history,0:w})
                q,x,tape=b,0,{-1:history,0:bit};trace=[]
                for steps in range(1,21):
                    assert x in (-1,0)
                    trace.append([q,x,tape[-1],tape[0]])
                    wr,dr,q=rows[q,tape[x]];tape[x]=wr;x+=1 if dr else -1
                    if (q,x,tape)==goal:break
                else:raise AssertionError(('local fold',old,bit))
                cases.append(dict(old=old,history=history,read=bit,steps=steps,trace=trace))
    return dict(cases=cases,incoming_rows=[r for a,b,_ in folds for q in (a,b) for r in incoming[q]])

def dense(rows):
    states={q for q,b in rows};assert len(states)==194 and HALT not in states
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    assert {n for w,d,n in rows.values()}-states=={HALT}
    order=[START];labels={START:0}
    for q in order:
        for bit in (0,1):
            n=rows[q,bit][2]
            if n!=HALT and n not in labels:labels[n]=len(order);order.append(n)
    assert len(order)==194
    return {(labels[q],b):(w,d,194 if n==HALT else labels[n]) for (q,b),(w,d,n) in rows.items()},order+[HALT]

def startup(rows,path):
    h=-2;physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    expected={h-1,h+48}|{h+i for i,bit in enumerate(path) if bit}
    p=h+49
    for v in physical:p+=1;expected.update(range(p,p+v+1));p+=v+1
    q,x,ones=START,0,set()
    for step in range(1,100001):
        w,d,q=rows[q,int(x in ones)];(ones.add if w else ones.discard)(x);x+=1 if d else -1
        assert q!=HALT
        if (q,x,ones)==(84,h,expected):
            return dict(steps=step,state=q,head=x,one_cells=sorted(ones),physical_file=physical,complete_tape_equality=True)
    raise AssertionError('Exact complete blank initialization failed')

def build(name,output,full=True):
    assert __debug__ and not sys.flags.optimize
    want,site_count,outcome_count,steps=EXPECTED[name]
    nopush=name=='PA194QNS'
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    primary=read_table(ROOT/'inputs/primary.native.tm')
    assert sha(table_text(primary).encode())=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    c.machine=lambda:(primary,[])
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(ROOT/'inputs/q.grammar.json')
    folds=json.loads((ROOT/'inputs/q.folds.json').read_text())
    parent_raw,_,_=c.build(grammar)
    if nopush:parent_raw[164,1]=(1,True,114)
    parent,_=fold(parent_raw,folds)
    if nopush:assert parent==read_table(ROOT/'inputs/parent_qn.native.tm')
    c.raw_nodes=lambda:nodes(nopush,False)
    parent_sites,parent_instructions,_=c.source(grammar)
    if nopush:
        assert json.loads(json.dumps(parent_instructions))==json.loads((ROOT/'inputs/parent_qn.instructions.json').read_text())
        assert json.loads(json.dumps(dict(sites=parent_sites,instructions=parent_instructions)))==json.loads((ROOT/'inputs/parent_qn.source.json').read_text())
    raw=dict(parent_raw)
    assert raw[38,1]==(1,True,20) and raw[310,1]==(1,True,62)
    raw[38,1]=(1,True,30);raw[310,1]=(1,True,330)
    raw[330,0]=(0,True,63);raw[330,1]=(1,False,73)
    folds.append([41,330,[[0,False,31],[1,False,46]]])
    rows,alias=fold(raw,folds);local=check_folds(raw,rows,folds,alias)
    assert len(raw)==404 and len(local['cases'])==32
    direct=dict(parent)
    direct[28,0]=(0,True,330);direct[70,0]=(0,True,330)
    direct[38,1]=(1,True,30);direct[310,1]=(1,True,330)
    del direct[41,0];del direct[41,1]
    direct[330,0]=(0,False,31);direct[330,1]=(1,False,46)
    assert rows==direct,'Grammar/fold construction differs from the eight-row patch.'
    c.raw_nodes=lambda:nodes(nopush,True)
    sites,instructions,contracts=c.source(grammar)
    prefix=3649 if nopush else 3668
    assert instructions[:prefix]==parent_instructions[:prefix]
    assert instructions[prefix:]==[('inc',5,prefix+1),('jump',0)]
    assert len(sites)==site_count and len(contracts)==outcome_count
    assert len(parent_sites)==len(sites)+3
    assert all(rows[q,b]==primary[q,b] for q in c.BOXSTATES for b in (0,1))
    validation=c.validate(rows,contracts) if full else None
    if full:assert validation==dict(ok=True,contracts=outcome_count,max_steps=490,total_steps=steps)
    seed=startup(rows,sites[25][0]);assert seed['steps']==58004
    d,labels=dense(rows);assert sha(table_text(d).encode())==want
    for filename,table in [('machine.native.tm',rows),('machine.tm',d),('raw.native.tm',raw),('parent.native.tm',parent)]:
        (output/filename).write_bytes(table_text(table).encode('ascii'))
    for filename,value in [('labels.json',labels),('folds.json',folds),('local_cases.json',local),
        ('nodes.json',nodes(nopush,True)),('instructions.json',instructions),('parent.instructions.json',parent_instructions),
        ('sites.json',[[''.join(map(str,p)),op,arg] for p,op,arg in sites])]:dump(output/filename,value)
    (output/'source.json').write_text(json.dumps(dict(sites=sites,instructions=instructions),sort_keys=True)+'\n')
    receipt=dict(status='PASS',family=name,working_states=194,transition_rows=388,native_start=START,native_halt=HALT,
        dense_start=0,dense_halt=194,raw_states=202,fixed_states=135,AX_readers=67,AX_folds=7,controller_folds=1,
        folds=8,simultaneous_fold_cases=32,source_sites=site_count,source_outcomes=outcome_count,
        source_prefix_identical_to_parent=prefix,removed_source_sites=3,
        generic_runtime_performed=full,symbolic_runtime=validation,startup=seed,
        arithmetic_box_rows_unchanged=True,graph_reachable_working_states=194,
        dense_sha256=want,native_sha256=sha(table_text(rows).encode()),
        physical_register_map=c.PHYSICAL,
        kernel_checked=False,scope='Exact reconstruction, complete source binding, simultaneous local folds, symbolic register contracts, and full blank startup. Ordinary mathematical PA calibration is documented separately.')
    dump(output/'construction_receipt.json',receipt)
    print(json.dumps({k:receipt[k] for k in ['family','working_states','source_sites','source_outcomes','dense_sha256','symbolic_runtime']},indent=2),flush=True)
    return receipt

if __name__=='__main__':
    if not __debug__:raise SystemExit('Use Python without -O.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family',choices=list(EXPECTED),default='PA194QNS')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--quick',action='store_true',help='Skip only the construction symbolic replay.')
    args=parser.parse_args()
    build(args.family,args.output or Path(tempfile.mkdtemp(prefix=args.family.lower()+'-')),not args.quick)
