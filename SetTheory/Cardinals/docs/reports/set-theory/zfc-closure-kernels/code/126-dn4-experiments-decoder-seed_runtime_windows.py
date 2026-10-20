#!/usr/bin/env python3
"""Discovery projection of complete symbolic instruction traces from a seed invariant.

Every literal configuration is projected using regular-language overapproximations.
Bulk scan/list interiors use the independently checked global bit invariant, a
conservative fallback. This discovery output does not itself certify a fold:
a promoted table must rerun all restricted instruction contracts and exact boot.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import sys,json,time,hashlib,argparse
sys.path.insert(0,str(Path(__file__).parent))
from analyze import v,P,c
sys.path.insert(0,str(P/'baseline226/vendor/proveit'))
import symbolic_runtime as e

@lru_cache(None)
def lens(n,k):
    if not any(n[1:]):return (min(n[0],k),)
    if n[0]>=k:return (k,)
    reachable={0}
    for coeff in set(n[1:])-{0}:
        reachable|={min(k,x+j*coeff) for x in tuple(reachable) for j in range(k//coeff+2)}
    return tuple(sorted({min(k,n[0]+x)for x in reachable}))

def trunc(atoms,k):
    out=[];minimum=0
    for a in atoms:
        out.append(a)
        if a[0]=='run':minimum+=a[2][0]
        if a[0] in ('blank','opaque') or minimum>=k:break
    return tuple(out)

@lru_cache(None)
def prefixes(atoms,k):
    if k==0:return (0,)
    assert atoms,('short projected tape',k)
    a,*rest=atoms;rest=tuple(rest)
    if a[0]=='blank':return (0,)
    if a[0]=='opaque':return tuple(range(1<<k))
    if a[0]=='list':
        # Arbitrary finite list. Reversal reverses each block and list order.
        family,rev=a[1],a[3]
        block=tuple(e.block(e.var(11),family))
        if rev:block=tuple(e.rev(block))
        return tuple(sorted(set(prefixes(rest,k))|set(prefixes(trunc(block+(a,)+rest,k),k))))
    assert a[0]=='run'
    words=set()
    for n in lens(a[2],k):
        low=(1<<n)-1 if a[1] else 0
        if n==k:words.add(low)
        else:
            for word in prefixes(trunc(rest,k-n),k-n):words.add(low|(word<<n))
    return tuple(sorted(words))


def initial_values(site,positive,masks,cutoff,modulus):
    pc,op,arg=site
    values=[]
    for i,mask0 in enumerate(masks):
        mask=mask0
        if op=='CD' and i==arg:mask=mask&~1 if positive else mask&1
        if not mask:return None
        exact=[n for n in range(cutoff)if mask>>n&1]
        large=[n for n in range(cutoff,cutoff+modulus)if mask>>(cutoff+n%modulus)&1]
        minimum=min(exact+large)
        if len(exact)==1 and not large:values.append(e.num(minimum))
        else:values.append(e.add(e.num(minimum),e.var(2+i)))
    return values


def restricted_case(table,lemmas,site,positive,values,observe=None,bulk=None):
    pc,op,arg=site
    physical=[None]*9
    for i,j in enumerate(e.r.PHY):physical[j]=values[i]
    result=physical.copy();overflow=0;delta=0;extra=None
    if op=='CI':
        result[e.r.PHY[arg]]=e.add(result[e.r.PHY[arg]],e.num(1));successor,overflow=e.r.inc(pc);extra=1
    elif op=='CD' and positive:
        result[e.r.PHY[arg]]=e.minus1(result[e.r.PHY[arg]]);successor,overflow=e.r.inc(pc);delta=1
    elif op in ('CD','CB'):successor,overflow=e.r.inc(e.r.strip(pc,'0',arg if op=='CB'else 1))
    elif op=='CC':successor=e.r.strip(pc,'1',arg)
    elif op=='CH':successor=''
    else:raise AssertionError(site)
    state=e.State(96,[e.bit(1),e.BLANK],[e.bit(int(b))for b in pc]+[e.run(0,e.add(e.var(1),e.num(64-len(pc)))),e.bit(1)]+e.file_bits(physical))
    target=e.State(96,[e.bit(1),e.BLANK],[e.bit(int(b))for b in successor]+[e.run(0,e.add(e.var(1),e.num(64+delta+overflow-len(successor)))),e.bit(1)]+e.file_bits(result,extra))
    target_key=target.key();clock=e.ZERO;motion=e.ZERO;rows=set()
    for count in range(4000):
        key=state.key()
        if observe is not None:observe(state)
        if count and((op=='CH'and state.q==254)or(op!='CH'and key==target_key)):
            assert e.nonnegative(clock)and clock[0]>0
            if op!='CH':assert motion==e.num(-overflow)
            return count,rows
        clock,motion,event=state.step(table,lemmas,clock,motion)
        if event[0]!='list':rows.add(event[1][:2])
        if bulk is not None and event[0]!='literal':bulk(event)
    raise AssertionError(('restricted case did not close',site,positive,state.key(),target_key))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--basis',type=Path,default=Path(__file__).parent/'full_dn4');ap.add_argument('--facts',type=Path,default=Path(__file__).parent/'facts/dn4_reachable_registers.json');ap.add_argument('--radius',type=int,default=6);ap.add_argument('--output',type=Path,default=Path(__file__).parent/'dn4_seed_windows.txt');ap.add_argument('--limit',type=int);a=ap.parse_args()
    basis=a.basis;L=R=a.radius;W=2*L+1;N=1<<W;tic=time.monotonic()
    norm,start=v.parse_table((basis/'simplified.tm').read_bytes());mp={int(k):z for k,z in json.loads((basis/'state_map.json').read_text()).items()};mp[254]=254;inv={z:q for q,z in mp.items()};old={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in norm.items()}
    sites=json.loads((basis/'sites225.json').read_text());info=json.loads(a.facts.read_text());assert info['source_sha256']==hashlib.sha256((basis/'sites225.json').read_bytes()).hexdigest()
    bf,_=v.bit_invariant(norm,start,max(L,R));allowed={}
    for q,fs in bf.items():
        allowed[q]=sum(1<<m for m in range(N)if fs is not None and all(((m>>(L+k))&1)==b for k,b in fs.items()if-L<=k<=R))
    seen={q:0 for q in bf};reverse={k:[int(f'{x:0{k}b}'[::-1],2)for x in range(1<<k)]for k in(L,L+1)};observed=set();bulkstates=set()
    def observe(state):
        q=inv[state.q]
        if seen[q]==allowed[q]:return
        if state.direction==1:kl,kr=L,R+1
        else:kl,kr=L+1,R
        lp=prefixes(trunc(state.left,kl),kl);rp=prefixes(trunc(state.right,kr),kr);sig=(q,state.direction,lp,rp)
        if sig in observed:return
        observed.add(sig);x=0
        for left in lp:
            low=reverse[kl][left]
            for right in rp:x|=1<<(low|(right<<kl))
        seen[q]|=x&allowed[q]
    lemmas,blocks=e.prove_blocks(old)
    blockstates=set()
    for rec in blocks:
        for event in rec['trace']:
            if event[0]!='list':blockstates.add(inv[event[1][0]])
    def bulk(event):
        qs=blockstates if event[0]=='list'else{inv[event[1][0]]}
        for q in qs:seen[q]=allowed[q];bulkstates.add(q)
    count=steps=0;rows=set();fails=[]
    for i,site in enumerate(sites):
        masks=info['facts'][i]
        if masks is None:continue
        for pos in((False,True)if site[1]=='CD'else(False,)):
            values=initial_values(site,pos,masks,info['cutoff'],info['modulus'])
            if values is None:continue
            try:n,rr=restricted_case(old,lemmas,site,pos,values,observe,bulk)
            except Exception as exc:raise RuntimeError((i,site,pos,exc))from exc
            count+=1;steps+=n;rows|=rr
        if count and count%500<2:print('PROGRESS',i,count,steps,len(observed),'secs',time.monotonic()-tic,flush=True)
        if a.limit and count>=a.limit:break
    # Exact literal prefix to the already calibrated complete seed frame.
    boot=json.loads((basis/'startup.json').read_text());q=start;head=0;ones=set();bootseen=Counter()
    for step in range(boot['steps']+1):
        mask=sum(1<<(k+L)for k in range(-L,R+1)if head+k in ones);seen[q]|=1<<mask;bootseen[q]+=1
        if step==boot['steps']:break
        w,d,q=norm[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    assert q==boot['state']and head==boot['head']and sorted(ones)==boot['ones']
    a.output.parent.mkdir(exist_ok=True,parents=True)
    with a.output.open('w')as f:
        for q in sorted(seen):
            x=seen[q]
            while x:
                bit=x&-x;m=bit.bit_length()-1;f.write(f'{q} {m}\n');x-=bit
    rec=dict(status='SEED_RESTRICTED_SYMBOLIC_RUNTIME_PROJECTION_DISCOVERY',cases=count,symbolic_steps=steps,rows=len(rows),contexts=sum(x.bit_count()for x in seen.values()),state_contexts={q:x.bit_count()for q,x in seen.items()},bulk_fallback_states=sorted(bulkstates),L=L,R=R,seconds=time.monotonic()-tic,language_projections=len(observed),prefix_cache=list(prefixes.cache_info()),source_sha256=info['source_sha256'],table_sha256=hashlib.sha256((basis/'simplified.tm').read_bytes()).hexdigest(),window_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),boot_steps=boot['steps'],scope='Discovery only. Whole restricted instruction proofs passed on the original table. Proposed folds require independent whole runtime replay and complete startup equality; this projection is not a claimed formal invariant certificate.')
    c.dump(a.output.with_suffix('.json'),rec);print(json.dumps({k:z for k,z in rec.items()if k!='state_contexts'},indent=2),flush=True)
if __name__=='__main__':main()
