#!/usr/bin/env python3
"""Independent universal literal-tape simulation for PA194AX11H/QAX11H.

No compiler or arithmetic-box oracle is imported. Four generic list
identities are rederived from the supplied literal transitions; every
source increment, both decrement outcomes, every jump and halt are checked
for arbitrary natural registers, affine zero gap and arbitrary nonempty
finite spare list. This is executable mathematical evidence, not Lean.
"""
from pathlib import Path
import sys,json,argparse,tempfile,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def read(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip()or line.lstrip().startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R')
        rows[q,b]=(w,d,n)
    qs={q for q,b in rows};assert set(rows)=={(q,b)for q in qs for b in(0,1)}
    halt={n for w,d,n in rows.values()}-qs;assert len(halt)==1
    return rows,qs,next(iter(halt))

def check(directory,out):
    assert __debug__ and not sys.flags.optimize
    rows,qs,halt=read(directory/'machine.native.tm')
    dense,dqs,dh=read(directory/'machine.tm');labels=json.loads((directory/'labels.json').read_text())
    assert len(qs)==194 and dqs==set(range(194))and halt==254 and dh==194
    assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254
    assert {(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==rows
    meta=json.loads((ROOT/'expected.json').read_text())
    family=json.loads((directory/'receipt.json').read_text())['family']
    target=meta[family]
    assert sha(directory/'machine.tm')==target['dense_sha256']
    sites=json.loads((directory/'sites.json').read_text())
    sites=[[''.join(map(str,p))if isinstance(p,list)else p,op,a]for p,op,a in sites]
    ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,ops[op],a]for p,op,a in sites]
    graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert instructions==json.loads((directory/'instructions.json').read_text())and len(sites)==target['sites']
    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in qs|{halt}:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in qs|{halt}})==195 and mapping[84]==96 and mapping[254]==254
    table={(mapping[q],b):(w,1 if d=='R'else -1,mapping[n])for(q,b),(w,d,n)in rows.items()}
    physical=(6,2,0,4,3,7,8,5,1);runtime.PHY=physical
    lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
    contracts=[];steps=0;maximum=0
    for i,site in enumerate(mapped):
        for positive in([False,True]if site[1]=='CD'else[False]):
            r=sym.case(table,lemmas,site,positive)
            steps+=r['symbolic_steps'];maximum=max(maximum,r['symbolic_steps'])
            contracts.append(dict(site=i,positive=positive,duration=r['duration'],motion=r['motion'],symbolic_steps=r['symbolic_steps']))
        if(i+1)%1000==0:print('Literal source sites checked',i+1,flush=True)
    assert len(contracts)==target['contracts']
    # Independently simulate complete startup with an array, not a set.
    tape=bytearray(20000);origin=10000;head=origin;q=74
    for step in range(target['startup']):
        assert 0<=head<len(tape)and q!=254
        w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d=='R'else -1
    assert(q,head-origin)==(84,-2)
    path=sites[25][0]
    frame=bytearray([1]+[int(b)for b in path]+[0]*(48-len(path))+[1])
    logical=[2]+[0]*8;values=[None]*9
    for i,j in enumerate(physical):values[j]=logical[i]
    for v in values+[1]*26:frame.extend([0]+[1]*(v+1))
    expected=bytearray(len(tape));expected[head-1:head-1+len(frame)]=frame
    assert tape==expected,'Whole startup tape disagrees.'
    out.mkdir(parents=True,exist_ok=True)
    encoded=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (out/'contracts.json').write_bytes(encoded)
    (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    receipt=dict(status='PASS',family=family,working_states=194,transition_rows=388,source_sites=len(sites),source_contracts=len(contracts),symbolic_steps=steps,maximum_symbolic_steps=maximum,minimum_positive_duration_constant=min(x['duration'][0]for x in contracts),generic_list_lemmas=4,arithmetic_box_oracles=False,independent_cfg_resolvers_agree=True,complete_startup_tape_equal=True,startup_steps=target['startup'],dense_native_conjugacy=True,dense_sha256=sha(directory/'machine.tm'),native_sha256=sha(directory/'machine.native.tm'),contracts_sha256=hashlib.sha256(encoded).hexdigest(),register_scope='nine independent arbitrary natural values and both decrement outcomes',spare_scope='arbitrary finite nonempty list of arbitrary natural values',gap_scope='48+n for arbitrary natural n, source address deducted',kernel_checked=False)
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--machine',type=Path,default=ROOT/'machine');p.add_argument('--output',type=Path);a=p.parse_args()
    check(a.machine,a.output or Path(tempfile.mkdtemp(prefix='pa194ax11-literal-')))
