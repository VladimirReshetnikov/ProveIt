#!/usr/bin/env python3
"""Independently check the literal PA194D table, source map, and blank seed.

No compiler or arithmetic-box oracle is imported. Four list-sweep lemmas
are derived from the literal table, then all source outcomes are checked
over arbitrary natural primary values, gap, and nonempty finite spare list.
"""
from pathlib import Path
import hashlib,json,sys,time

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source

sym.HEADER_BASE=48
runtime.PHY=(6,2,0,4,3,7,8,5,1)
NAME='pa194d';M=ROOT/'machine';OUT=ROOT/'evidence'
def sha(data):return hashlib.sha256(data).hexdigest()
def parse(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip():continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R')
        rows[q,b]=(w,d,n)
    return rows
def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')

def main():
    assert __debug__ and not sys.flags.optimize,'Run without -O.'
    started=time.monotonic();OUT.mkdir(exist_ok=True)
    native=M/(NAME+'.native.tm');rows=parse(native)
    states={q for q,b in rows};assert len(states)==194 and len(rows)==388
    assert set(rows)=={(q,b)for q in states for b in(0,1)}
    assert {n for w,d,n in rows.values()}-states=={254}
    assert sha(native.read_bytes())=='bc8ab6c58badd137535938c9810e39d19152c49dd2eb26ef4ea07dbcf3157231'
    dense_path=M/(NAME+'.tm');dense=parse(dense_path)
    assert{q for q,b in dense}==set(range(194))
    assert{n for w,d,n in dense.values()}-set(range(194))=={194}
    labels=json.loads((M/(NAME+'.labels.json')).read_text())
    assert len(labels)==195 and labels[0]==74 and labels[-1]==254 and len(set(labels))==195
    assert{(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==rows
    sites=json.loads((M/(NAME+'.sites.json')).read_text())
    opcode={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,opcode[op],arg]for p,op,arg in sites]
    arithmetic_graph,_=source.graph_arithmetic(mapped)
    assert arithmetic_graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[effect[0]]]+effect[1:]+targets for effect,targets in arithmetic_graph]
    assert instructions==json.loads((M/(NAME+'.instructions.json')).read_text())
    assert len(sites)==3649 and max(len(p)for p,op,arg in sites)<=48
    mapping={int(k):v for k,v in json.loads((ROOT/'reference/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in states|{254}})==195
    assert mapping[84]==96 and mapping[254]==254
    table={(mapping[q],b):(w,1 if d=='R'else-1,mapping[n])for(q,b),(w,d,n)in rows.items()}
    lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
    contracts=[];total=0;maximum=0
    for i,site in enumerate(mapped):
        for positive in([False,True]if site[1]=='CD'else[False]):
            result=sym.case(table,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append({'site':i,'positive':positive,'duration':result['duration'],
                'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
        if(i+1)%500==0:print('verified',i+1,'of',len(sites),'source sites',flush=True)
    assert len(contracts)==4751
    # Independent bytearray startup. No set-based builder simulator is used.
    tape=bytearray(20000);origin=10000;head=origin;q=74
    for step in range(58168):
        assert q!=254 and 0<=head<len(tape)
        w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d=='R'else-1
    assert q==84 and head-origin==-2
    path=sites[25][0]
    frame=bytearray([1]+[int(b)for b in path]+[0]*(48-len(path))+[1])
    logical=[2]+[0]*8;physical=[None]*9
    for i,j in enumerate(runtime.PHY):physical[j]=logical[i]
    for value in physical+[1]*26:frame.extend([0]+[1]*(value+1))
    expected=bytearray(len(tape));first=head-1;expected[first:first+len(frame)]=frame
    assert tape==expected,'Complete blank-start tape differs.'
    encoded=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (OUT/'independent_contracts.json').write_bytes(encoded)
    dump(OUT/'independent_list_lemmas.json',blocks)
    dump(OUT/'independent_blank_seed.json',{'steps':58168,'state':q,'head':head-origin,
        'site':25,'path':path,'logical_registers':logical,'physical_registers':physical,
        'spares':[1]*26,'ones':[i-origin for i,b in enumerate(tape)if b]})
    receipt={'status':'PASS','working_states':194,'transition_rows':388,'source_sites':len(sites),
        'source_contracts':len(contracts),'independent_source_resolvers_agree':True,
        'generated_instruction_map_matches':True,'four_list_lemmas_rederived_from_table':True,
        'arithmetic_box_oracles':False,'symbolic_steps':total,'maximum_symbolic_steps':maximum,
        'minimum_duration_constant':min(x['duration'][0]for x in contracts),
        'whole_blank_tape_equal':True,'startup_steps':58168,'dense_conjugacy':True,
        'native_sha256':sha(native.read_bytes()),'dense_sha256':sha(dense_path.read_bytes()),
        'contracts_sha256':sha(encoded),'kernel_checked':False,
        'scope':'All natural primary values and both decrement outcomes; arbitrary natural gap and arbitrary nonempty finite spare list; full tape with zero exterior.',
        'seconds':round(time.monotonic()-started,6)}
    dump(OUT/'independent_receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
