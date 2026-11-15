#!/usr/bin/env python3
"""Independent finite-premise checker for the written LCSF3 iPRA proof.

Checks full table identity, complete-tape local identities, source reachability,
fixed-address use, exact initialization, and canonical instruction endpoints.
No bounded run is used as evidence for unbounded nonhalting.
"""
import argparse, hashlib, itertools, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'reference/composites/machines/PA194LC_AX11H_SF'
LC=ROOT/'reference/references/lc_ax11h'
PHYSICAL=[6,2,0,4,3,7,8,5,1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    t={}
    for line in p.read_text().splitlines():
        a=line.split();assert len(a)==5
        q,b,w,d,n=a;q,b,w,n=map(int,(q,b,w,n));assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in t;t[q,b]=(w,1 if d=='R' else -1,n)
    return t
def shape(t,start,halt):
    s={q for q,b in t};assert len(s)==194 and halt not in s and len(t)==388
    assert set(t)=={(q,b) for q in s for b in (0,1)}
    assert {n for w,d,n in t.values()}-s=={halt}
    seen={start};queue=[start]
    for q in queue:
        for b in (0,1):
            n=t[q,b][2]
            if n!=halt and n not in seen:seen.add(n);queue.append(n)
    assert seen==s
    # Greatest ordinary deterministic action congruence, respecting the halt.
    cls={q:0 for q in s};cls[halt]=-1
    while True:
        ids={};new={halt:-1}
        for q in sorted(s):
            key=tuple((w,d,cls[n]) for b in (0,1) for w,d,n in [t[q,b]])
            if key not in ids:ids[key]=len(ids)
            new[q]=ids[key]
        if all((cls[a]==cls[b])==(new[a]==new[b]) for a in s for b in s):break
        cls=new
    assert len(ids)==194
    return {'working_states':194,'rows':388,'graph_reachable_states':194,'ordinary_action_congruence_classes':194}
def step(t,c):
    q,h,ones=c
    if q==254:return c
    w,d,n=t[q,int(h in ones)];ones=set(ones);(ones.add if w else ones.discard)(h)
    return n,h+d,ones
def steps(t,c,n):
    for _ in range(n):c=step(t,c)
    return c
def frame(path,regs,gap=0,spares=None):
    if spares is None:spares=[1]*26
    h=-2;ones={h-1,h+48+gap}
    ones.update(h+i for i,b in enumerate(path) if b=='1')
    values=[0]*9
    for logical,physical in enumerate(PHYSICAL):values[physical]=regs[logical]
    pos=h+49+gap
    for v in values+spares:
        pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
    return 84,h,ones
def main():
    p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,default=ROOT/'candidate');p.add_argument('--output',type=Path);a=p.parse_args()
    assert __debug__
    expected={'machine.native.tm':'b741261b92a17256dfcbc9c6d3ee38d4fb27a3eee9be180a54ca63dca1c13cfe','machine.tm':'2e5684567cd6e6e59fd99b5b093071533bcef6a01012dd2c6e41d52c645d2768'}
    assert sha(PARENT/'machine.native.tm')=='23c40299b43056202f3f9bbe562e52f35b23dc25c13e0cb5e4f556444d86d0a5'
    for f,h in expected.items():assert sha(a.candidate/f)==h
    old,new,dense=read(PARENT/'machine.native.tm'),read(a.candidate/'machine.native.tm'),read(a.candidate/'machine.tm')
    labels=json.loads((a.candidate/'labels.json').read_text())
    assert labels[0]==74 and labels[-1]==254 and len(labels)==len(set(labels))==195
    assert {(labels[q],b):(w,d,labels[n]) for(q,b),(w,d,n)in dense.items()}==new
    assert [(k,old[k],new[k]) for k in sorted(old) if old[k]!=new[k]]==[((190,1),(1,-1,73),(0,-1,42))]
    for t in (old,new):
        assert [(q,b,w,d) for(q,b),(w,d,n)in sorted(t.items())if n==190]==[(139,1,1,1)]
    assert old[73,1]==(1,1,83) and old[83,1]==(0,-1,42)
    local=[]
    for free in itertools.product((0,1),repeat=3):
        ones={-1,0}|{i for i,b in zip((-2,1,2),free)if b}
        c=(190,0,ones);x=steps(old,c,3);y=step(new,c);assert x==y
        local.append({'free_bits':list(free),'complete_tape_equal':True,'end_state':x[0],'end_head':x[1]})
    sites=json.loads((LC/'sites.json').read_text());ins=json.loads((LC/'instructions.json').read_text())
    assert len(sites)==len(ins)==3671
    startup={}
    expected_frame=frame(sites[25][0],[2]+[0]*8)
    for name,t in [('parent',old),('child',new)]:
        c=(74,0,set());hits=0
        for tick in range(1,57919):
            hits+=int(c[0]==190 and c[1]in c[2]);c=step(t,c)
        assert c==expected_frame and hits==0
        startup[name]={'steps':57918,'state':c[0],'head':c[1],'one_cells':sorted(c[2]),'shortcut_uses':hits,'entire_seed_frame_equal':True}
    affected=[]
    for i,(path,op,arg)in enumerate(sites):
        # Exterior is deliberately unavailable: only fixed source address bits exist.
        q,h,ones=84,0,{j for j,b in enumerate(path)if b=='1'};reads=[]
        for tick in range(100):
            if h<0 or h>=len(path):break
            reads.append(h)
            if q==190 and h in ones:
                affected.append({'site':i,'path':path,'instruction':ins[i],'decoder_steps':tick,'relative_head':h,'reads':reads})
                break
            q,h,ones=step(new,(q,h,ones))
    assert len(affected)==61
    affected_ids={x['site']for x in affected}
    r=[2]+[0]*8;i=25;history=[]
    for tick in range(32687):
        if i in affected_ids:break
        history.append([tick,i,list(r)]);history=history[-5:]
        inst=ins[i]
        if inst[0]=='inc':r[inst[1]]+=1;i=inst[2]
        elif inst[0]=='dec':
            _,j,z,pos=inst
            if r[j]:r[j]-=1;i=pos
            else:i=z
        elif inst[0]=='jump':i=inst[1]
        else:raise AssertionError(('unexpected source halt',tick))
    assert tick==32686 and i==630 and r==[4,4,9,0,0,0,0,6,0]
    first=next(x for x in affected if x['site']==630)
    assert first['decoder_steps']==24 and first['relative_head']==22 and min(first['reads'])==0 and max(first['reads'])==22
    c=frame(sites[i][0],r);endpoints={}
    for name,t,length in [('parent',old,66),('child',new,64)]:
        end=steps(t,c,length);assert end[0]==84 and end[1]==-2
        endpoints[name]=end
    assert endpoints['parent']==endpoints['child']==frame(sites[625][0],r)
    result={'status':'PASS','reconstructed_after_environment_reset':True,'native_sha256':expected['machine.native.tm'],'dense_sha256':expected['machine.tm'],
        'shape':shape(new,74,254),'dense_shape':shape(dense,0,194),'unique_predecessor':[139,1,1,'R',190],
        'local_cases':local,'local_identity':'(190,2*l+1,2*r+1) ->^3 (42,l,4*r+1) equals child one step',
        'startup':startup,'affected_source_sites':affected,
        'first_source_use':{'steps':32686,'site':630,'registers':r,'preceding_states':history,'physical_decoder':first},
        'canonical_instruction':{'parent_steps':66,'child_steps':64,'complete_endpoint_equal':True,'successor_site':625},
        'relative_ipra_witness_bounds':{'parent_to_child':'t','child_to_parent':'3*t'},
        'limitations':['Graph reachability is not blank-run reachability.','Source-frame theorem transfers the source event; no scalar replay of the entire physical source prefix.','Absolute calibration and rule soundness are inherited written proofs, not a completed Lean endpoint.']}
    out=a.output or a.candidate/'verification.json';out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','dense_sha256':expected['machine.tm'],'states':194,'startup':57918,'fixed_address_sites':len(affected),'first_source_use':32686,'local_cases':len(local)},indent=2))
if __name__=='__main__':main()
