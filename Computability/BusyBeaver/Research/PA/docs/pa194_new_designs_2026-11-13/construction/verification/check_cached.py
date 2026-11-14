#!/usr/bin/env python3
"""Check PA194C literally on arbitrary complete register frames.
No compiler, allocator or arithmetic-box oracle is imported. Four list
lemmas are proved from the literal table, followed by all source branches.
"""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48
if not __debug__:raise RuntimeError('Assertions required.')
PHY=(6,2,0,4,3,7,8,5,1)

def sha(data):return hashlib.sha256(data).hexdigest()
def read(p,halt):
    table={}
    for ln in p.read_text().splitlines():
        q,b,w,d,t=ln.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in table
        table[q,b]=(w,1 if d=='R'else -1,t)
    states={q for q,b in table}
    assert len(states)==194 and halt not in states
    assert set(table)=={(q,b)for q in states for b in(0,1)}
    assert {t for w,d,t in table.values()}-states=={halt}
    return table,states

def main():
    inp=ROOT/'candidate';out=HERE/'results';out.mkdir(exist_ok=True)
    table,states=read(inp/'pa194C.native.tm',254)
    dense,ds=read(inp/'pa194C.tm',194);assert ds==set(range(194))
    labels=json.loads((inp/'pa194C.labels.json').read_text())
    assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254
    assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==table
    reach=[74];seen={74}
    for q in reach:
        for b in(0,1):
            t=table[q,b][2]
            if t!=254 and t not in seen:seen.add(t);reach.append(t)
    assert reach+[254]==labels
    sites=json.loads((inp/'pa194C.sites.json').read_text());assert len(sites)==3649
    code={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,code[op],a]for p,op,a in sites]
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    ins=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert ins==json.loads((inp/'pa194C.instructions.json').read_text())
    assert ins==json.loads((ROOT/'inputs/195C.instructions.json').read_text())
    assert max(len(p)for p,op,a in sites)<=48
    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in states|{254}})==195
    assert mapping[84]==96 and mapping[254]==254
    symbolic={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in table.items()}
    runtime.PHY=PHY
    lemmas,blocks=sym.prove_blocks(symbolic);assert len(blocks)==4
    contracts=[];total=0;maximum=0
    for i,site in enumerate(mapped):
        for positive in([False,True]if site[1]=='CD'else[False]):
            result=sym.case(symbolic,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append({'site':i,'positive':positive,'duration':result['duration'],
              'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
        if(i+1)%500==0:print('194C checked source sites',i+1,flush=True)
    assert len(contracts)==4749
    # Independent bytearray blank simulator; complete tape equality.
    tape=bytearray(20000);origin=10000;head=origin;q=74
    for step in range(57922):
        assert q!=254 and 0<=head<len(tape)
        w,d,q=table[q,tape[head]];tape[head]=w;head+=d
    assert q==84 and head-origin==-2
    p=sites[25][0];frame=bytearray([1]+[int(b)for b in p]+[0]*(48-len(p))+[1])
    logical=[2]+[0]*8;physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
    expected=bytearray(len(tape));a=head-1;expected[a:a+len(frame)]=frame
    assert tape==expected
    enc=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (out/'contracts.json').write_bytes(enc)
    (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    seed={'steps':57922,'state':q,'head':head-origin,'ones':[i-origin for i,b in enumerate(tape)if b],
          'source_site':25,'source_path':p,'header_base':48,'logical_registers':logical,
          'physical_registers':physical,'spare_values':[1]*26}
    (out/'blank_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    receipt={'family':'PA194C','status':'PASS','working_states':194,'transition_rows':388,
      'native_sha256':sha((inp/'pa194C.native.tm').read_bytes()),
      'dense_sha256':sha((inp/'pa194C.tm').read_bytes()),'dense_conjugacy_exact':True,
      'source_sites':3649,'universal_source_outcomes':4749,
      'independent_cfg_resolvers_agree':True,'source_graph_equal_to_pinned195C':True,
      'symbolic_steps':total,'maximum_symbolic_steps':maximum,
      'minimum_positive_duration_constant':min(c['duration'][0]for c in contracts),
      'four_list_lemmas_rederived_from_literal_table':True,'arithmetic_box_oracles':False,
      'register_scope':'nine arbitrary natural values; both decrement outcomes',
      'spare_scope':'arbitrary finite nonempty list of arbitrary natural values',
      'startup_steps':57922,'whole_blank_tape_equal':True,'contracts_sha256':sha(enc),
      'kernel_checked':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
