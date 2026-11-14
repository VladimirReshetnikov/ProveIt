#!/usr/bin/env python3
"""Check PA194CSZ literally on arbitrary complete register frames.
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
    inp=ROOT/'machine_csz';out=HERE/'results_csz';out.mkdir(exist_ok=True)
    table,states=read(inp/'pa194CSZ.native.tm',254)
    dense,ds=read(inp/'pa194CSZ.tm',194);assert ds==set(range(194))
    labels=json.loads((inp/'pa194CSZ.labels.json').read_text())
    assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254
    assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==table
    reach=[74];seen={74}
    for q in reach:
        for b in(0,1):
            t=table[q,b][2]
            if t!=254 and t not in seen:seen.add(t);reach.append(t)
    assert reach+[254]==labels
    sites=json.loads((inp/'pa194CSZ.sites.json').read_text());assert len(sites)==3646
    code={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,code[op],a]for p,op,a in sites]
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    ins=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert ins==json.loads((inp/'pa194CSZ.instructions.json').read_text())
    parent_bytes=(ROOT/'referenceCS/pa194CS.instructions.json').read_bytes()
    assert sha(parent_bytes)=='e2f74c0fad95734738788b98e76dc3e11748c0819ad7ef2b2998f81e0140da87'
    old=json.loads(parent_bytes)
    assert len(old)==len(ins)==3646
    assert [i for i in range(len(ins)) if old[i]!=ins[i]]==[26]
    assert old[26]==['jump',34] and ins[26]==['dec',6,34,27]
    # Verify a finite inductive certificate without importing the builder.
    pairs=json.loads((inp/'positivity_pairs.json').read_text())
    relation={tuple(p)for p in pairs}
    assert len(relation)==len(pairs) and (25,1) in relation
    def abstract_next(program,pc,mask):
        z=program[pc]
        if z[0]=='halt':return set()
        if z[0]=='jump':return {(z[1],mask)}
        bit=1<<z[1]
        if z[0]=='inc':return {(z[2],mask|bit)}
        assert z[0]=='dec'
        return {(z[3],mask),(z[3],mask&~bit)} if mask&bit else {(z[2],mask)}
    for pc,mask in relation:
        assert 0<=pc<len(ins) and 0<=mask<512
        first=abstract_next(old,pc,mask);second=abstract_next(ins,pc,mask)
        assert first==second and first<=relation
    masks=sorted(m for pc,m in relation if pc==26)
    assert masks and all(not(m&64)for m in masks)
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
        if(i+1)%500==0:print('194CSZ checked source sites',i+1,flush=True)
    assert len(contracts)==4746
    # Independent bytearray blank simulator; exact entire tape match.
    p=sites[25][0];frame=bytearray([1]+[int(b)for b in p]+[0]*(48-len(p))+[1])
    logical=[2]+[0]*8;physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
    tape=bytearray(20000);origin=10000;head=origin;q=74
    expected=bytearray(len(tape));a=origin-3;expected[a:a+len(frame)]=frame
    for startup_steps in range(1,200001):
        assert q!=254 and 0<=head<len(tape)
        w,d,q=table[q,tape[head]];tape[head]=w;head+=d
        if q==84 and head-origin==-2 and tape==expected:break
    else:raise AssertionError('clean source seed not reached within explicit bound')
    assert q==84 and head-origin==-2 and tape==expected
    enc=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (out/'contracts.json').write_bytes(enc)
    (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    seed={'steps':startup_steps,'state':q,'head':head-origin,'ones':[i-origin for i,b in enumerate(tape)if b],
          'source_site':25,'source_path':p,'header_base':48,'logical_registers':logical,
          'physical_registers':physical,'spare_values':[1]*26}
    (out/'blank_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    receipt={'family':'PA194CSZ','status':'PASS','working_states':194,'transition_rows':388,
      'native_sha256':sha((inp/'pa194CSZ.native.tm').read_bytes()),
      'dense_sha256':sha((inp/'pa194CSZ.tm').read_bytes()),'dense_conjugacy_exact':True,
      'source_sites':3646,'universal_source_outcomes':4746,
      'independent_cfg_resolvers_agree':True,'source_zero_register_jump_bound_exactly':True,
      'independent_inductive_invariant_checked':True,'inductive_pairs':len(relation),'site26_masks':masks,
      'symbolic_steps':total,'maximum_symbolic_steps':maximum,
      'minimum_positive_duration_constant':min(c['duration'][0]for c in contracts),
      'four_list_lemmas_rederived_from_literal_table':True,'arithmetic_box_oracles':False,
      'register_scope':'nine arbitrary natural values; both decrement outcomes',
      'spare_scope':'arbitrary finite nonempty list of arbitrary natural values',
      'startup_steps':startup_steps,'whole_blank_tape_equal':True,'contracts_sha256':sha(enc),
      'kernel_checked':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
