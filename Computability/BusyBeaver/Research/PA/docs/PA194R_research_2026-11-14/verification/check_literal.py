#!/usr/bin/env python3
"""Independent literal-tape verification of the final-emitter zero-jump composition.

Adapted from the supplied PA194CS verification/check.py, retaining its attributed
literal symbolic execution library and source resolvers. No compiler or
arithmetic-box oracle is imported. Source3553 is changed independently from a
pinned PA194CS site list, and both decrement outcomes are checked universally.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48
PHY=(6,2,0,4,3,7,8,5,1)
if not __debug__:raise SystemExit('Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.')
sha=lambda b:hashlib.sha256(b).hexdigest()

def read(p):
    rows={}
    for ln in p.read_text().splitlines():
        q,b,w,d,t=ln.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows
        rows[q,b]=(w,1 if d=='R' else -1,t)
    states={q for q,b in rows}
    assert len(states)==194 and 254 not in states
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    assert {t for w,d,t in rows.values()}-states=={254}
    return rows,states

def text_table(table):
    return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n'
                   for (q,b),(w,d,t) in sorted(table.items()))

def dense(table,states):
    labels=[74];seen={74}
    for q in labels:
        for b in (0,1):
            t=table[q,b][2]
            if t!=254 and t not in seen:seen.add(t);labels.append(t)
    assert seen==states and len(labels)==194
    labels.append(254);inv={q:i for i,q in enumerate(labels)}
    result={(inv[q],b):(w,d,inv[t]) for (q,b),(w,d,t) in table.items()}
    assert {(labels[q],b):(w,d,labels[t]) for (q,b),(w,d,t) in result.items()}==table
    return result,labels

def next_pairs(code,pc,mask):
    op,*args=code[pc]
    if op=='halt':return ()
    if op=='jump':return ((args[0],mask),)
    reg=args[0];flag=1<<reg;assert 0<=reg<9
    if op=='inc':return ((args[1],mask|flag),)
    assert op=='dec'
    if mask&flag:return ((args[2],mask&~flag),(args[2],mask))
    return ((args[1],mask),)

def closure(code):
    found={(25,1)};todo=[(25,1)]
    for pc,mask in todo:
        for pair in next_pairs(code,pc,mask):
            assert 0<=pair[0]<len(code) and 0<=pair[1]<512
            if pair not in found:found.add(pair);todo.append(pair)
    return found

def verify(family='PA194F',reg=6,target=21,output=None):
    started=time.monotonic();inp=HERE.parent/'inputs';out=(output or HERE/'recorded')/family;out.mkdir(parents=True,exist_ok=True)
    native_input=inp/'pa194CS.native.tm';sites_input=inp/'pa194CS.sites.json';code_input=inp/'pa194CS.instructions.json'
    assert sha(native_input.read_bytes())=='00446d08d3c35909a11460a9e19507d53e8526ad822b94ce9a04c73951eb447b'
    assert sha(code_input.read_bytes())=='e2f74c0fad95734738788b98e76dc3e11748c0819ad7ef2b2998f81e0140da87'
    table,states=read(native_input);old_action=table[2066,1];table[2066,1]=(1,1,target)
    dtable,labels=dense(table,states)
    native_bytes=text_table(table).encode();dense_bytes=text_table(dtable).encode()
    (out/'machine.native.tm').write_bytes(native_bytes);(out/'machine.tm').write_bytes(dense_bytes)
    (out/'labels.json').write_text(json.dumps(labels)+'\n')
    oldsites=json.loads(sites_input.read_text());sites=json.loads(json.dumps(oldsites))
    assert len(sites)==3646 and sites[3553][1:]==['breakTo',1]
    sites[3553][1:]=['dec',reg]
    codes={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,codes[op],a] for p,op,a in sites]
    graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    old=json.loads(code_input.read_text())
    assert [(i,a,b) for i,(a,b) in enumerate(zip(old,instructions)) if a!=b]==[(3553,['jump',3637],['dec',reg,3637,3554])]
    common=closure(old);new_reach=closure(instructions);assert common==new_reach
    assert len(common)==263180
    assert all(next_pairs(old,p,m)==next_pairs(instructions,p,m) for p,m in common)
    assert all(v in common for p,m in common for v in next_pairs(old,p,m))
    masks=sorted(m for p,m in common if p==3553);assert masks and all(m&(1<<reg)==0 for m in masks)
    invariant={'pairs':len(common),'source3553_masks':masks,'register':reg,'register_zero_at3553':True,
               'old_new_successors_equal_on_closed_set':True,'initial_pc':25,'initial_mask':1,
               'sha256':sha(json.dumps(sorted(common),separators=(',',':')).encode())}
    (out/'sites.json').write_text(json.dumps(sites)+'\n')
    (out/'instructions.json').write_text(json.dumps(instructions)+'\n')
    (out/'invariant.json').write_text(json.dumps(invariant,indent=2)+'\n')
    assert max(len(p) for p,op,a in sites)<=48
    mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+10000)
    assert len({mapping[q] for q in states|{254}})==195
    assert mapping[84]==96 and mapping[254]==254
    symbolic={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in table.items()}
    runtime.PHY=PHY
    lemmas,blocks=sym.prove_blocks(symbolic);assert len(blocks)==4
    print(family,'four literal list lemmas rederived',flush=True)
    contracts=[];total=0;maximum=0
    for i,site in enumerate(mapped):
        for positive in ([False,True] if site[1]=='CD' else [False]):
            result=sym.case(symbolic,lemmas,site,positive)
            total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
            contracts.append({'site':i,'positive':positive,'duration':result['duration'],
                              'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
        if (i+1)%500==0:print(family,'checked',i+1,'of',len(sites),'source sites',flush=True)
    assert len(contracts)==4746
    # Independent finite-support blank simulator. Search for the specified entire
    # source25 seed, then check the zero exterior as well as all register/spare bits.
    tape=bytearray(20000);origin=10000;head=origin;q=74
    p=sites[25][0];frame=bytearray([1]+[int(bit) for bit in p]+[0]*(48-len(p))+[1])
    logical=[2]+[0]*8;physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
    expected=bytearray(len(tape));offset=origin-3;expected[offset:offset+len(frame)]=frame
    startup_steps=None
    for step in range(1000001):
        if q==84 and head-origin==-2 and tape==expected:
            startup_steps=step;break
        assert q!=254 and 0<=head<len(tape)
        w,d,q=table[q,tape[head]];tape[head]=w;head+=d
    assert startup_steps is not None,'Exact whole-tape seed not reached within startup bound.'
    assert tape==expected and q==84 and head-origin==-2
    enc=(json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (out/'contracts.json').write_bytes(enc);(out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    seed={'steps':startup_steps,'state':q,'head':head-origin,'ones':[i-origin for i,bit in enumerate(tape) if bit],
          'source_site':25,'source_path':p,'header_base':48,'logical_registers':logical,
          'physical_registers':physical,'spare_values':[1]*26}
    (out/'blank_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    receipt={'family':family,'status':'PASS','working_states':194,'transition_rows':388,
             'native_sha256':sha(native_bytes),'dense_sha256':sha(dense_bytes),'dense_conjugacy_exact':True,
             'source_sites':3646,'universal_source_outcomes':4746,'independent_cfg_resolvers_agree':True,
             'source_edit':{'site':3553,'before':['jump',3637],'after':['dec',reg,3637,3554]},
             'native_edit':{'row':[2066,1],'before':old_action,'after':table[2066,1]},
             'source_preservation_inductive_pairs':len(common),'register_zero_at_site3553':reg,
             'symbolic_steps':total,'maximum_symbolic_steps':maximum,
             'minimum_positive_duration_constant':min(c['duration'][0] for c in contracts),
             'four_list_lemmas_rederived_from_literal_table':True,'arithmetic_box_oracles':False,
             'register_scope':'Nine arbitrary natural register values; both outcomes of every decrement.',
             'spare_scope':'Arbitrary finite nonempty list of arbitrary natural spare values.',
             'startup_steps':startup_steps,'whole_blank_tape_equal':True,'contracts_sha256':sha(enc),
             'kernel_checked':False,'elapsed_seconds':round(time.monotonic()-started,3)}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,help='Directory for newly checked outputs (default: verification/recorded).')
    a=ap.parse_args()
    verify(output=a.output)
