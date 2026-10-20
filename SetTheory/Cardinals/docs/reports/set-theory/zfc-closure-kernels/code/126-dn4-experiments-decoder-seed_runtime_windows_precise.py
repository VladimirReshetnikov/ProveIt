#!/usr/bin/env python3
"""Refine seed-restricted symbolic trace projection, including bulk interiors.

This is a discovery driver. Its promotion gate is a separate complete symbolic
runtime proof of the proposed table on the inductive register invariant.
"""
from seed_runtime_windows import *

@lru_cache(None)
def lengths(expr,cap,domains):
    result={min(cap,expr[0])}
    for i,coeff in enumerate(expr[1:],1):
        if not coeff:continue
        choices=domains[i]
        if choices is None:choices=range(cap+1)
        result={min(cap,x+coeff*y)for x in result for y in choices}
    return tuple(sorted(result))

def domains_for(site,pos,masks,C,M,cap):
    ds=[None]*e.NV
    for i,mask in enumerate(masks):
        if site[1]=='CD'and i==site[2]:mask=mask&~1 if pos else mask&1
        possibilities=[n for n in range(C+M+cap+1)if mask>>(n if n<C else C+n%M)&1]
        low=min(possibilities);ds[2+i]=tuple(sorted({min(cap,n-low)for n in possibilities}))
    return tuple(ds)

@lru_cache(None)
def language(atoms,k):
    if k==0:return (0,)
    assert atoms
    a=atoms[0];rest=atoms[1:]
    if a[0]=='blank':return (0,)
    if a[0]=='opaque':return tuple(range(1<<k))
    if a[0]=='list':
        family,rev=a[1],a[2]
        # These lists range over independent arbitrary naturals, with all
        # possible finite list lengths, including zero.
        unknown=tuple(range(MAXCAP+1))
        block=(('run',0,(1,)),('run',1,tuple(range(1,MAXCAP+1))))if family=='B'else(('run',1,(1,)),('run',0,(1,)),('run',1,unknown))
        if rev:block=tuple(reversed(block))
        return tuple(sorted(set(language(rest,k))|set(language(block+(a,)+rest,k))))
    out=set()
    for n in {min(x,k)for x in a[2]}:
        low=(1<<n)-1 if a[1]else 0
        if n==k:out.add(low)
        else:
            for x in language(rest,k-n):out.add(low|(x<<n))
    return tuple(sorted(out))

MAXCAP=14

def main():
    global MAXCAP
    ap=argparse.ArgumentParser();ap.add_argument('--basis',type=Path,default=Path(__file__).parent/'full_dn4');ap.add_argument('--facts',type=Path,default=Path(__file__).parent/'facts/dn4_reachable_registers.json');ap.add_argument('--radius',type=int,default=6);ap.add_argument('--output',type=Path,default=Path(__file__).parent/'dn4_seed_precise_windows.txt');ap.add_argument('--limit',type=int);a=ap.parse_args()
    basis=a.basis;L=R=a.radius;K=max(L,R)+1;MAXCAP=2*K;W=L+R+1;N=1<<W;tic=time.monotonic()
    norm,start=v.parse_table((basis/'simplified.tm').read_bytes());mp={int(k):z for k,z in json.loads((basis/'state_map.json').read_text()).items()};mp[254]=254;inv={z:q for q,z in mp.items()};old={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in norm.items()}
    sites=json.loads((basis/'sites225.json').read_text());info=json.loads(a.facts.read_text());assert info['source_sha256']==hashlib.sha256((basis/'sites225.json').read_bytes()).hexdigest()
    bf,_=v.bit_invariant(norm,start,max(L,R));allowed={}
    for q,fs in bf.items():allowed[q]=sum(1<<m for m in range(N)if fs is not None and all(((m>>(L+k))&1)==b for k,b in fs.items()if-L<=k<=R))
    seen={q:0 for q in bf};reverse={k:[int(f'{x:0{k}b}'[::-1],2)for x in range(1<<k)]for k in(L,L+1)};observed=set();bulkseen=set();listseen=set();last=None;domains=(None,)*e.NV
    def encode_atoms(atoms,width):
        out=[];minimum=0
        for atom in atoms:
            kind=atom[0]
            if kind=='run':
                ls=lengths(atom[2],MAXCAP,domains)
                if ls==(0,):continue
                a=('run',atom[1],ls);minimum+=ls[0]
            elif kind=='list':a=('list',atom[1],atom[3])
            else:a=(kind,)
            out.append(a)
            if kind in('blank','opaque')or minimum>=width:break
        return tuple(out)
    def add_languages(q,d,left,right):
        if seen[q]==allowed[q]:return
        kl,kr=(L,R+1)if d==1 else(L+1,R)
        lp=language(left,kl);rp=language(right,kr);sig=(q,d,lp,rp)
        if sig in observed:return
        observed.add(sig);x=0
        for le in lp:
            low=reverse[kl][le]
            for ri in rp:x|=1<<(low|(ri<<kl))
        seen[q]|=x&allowed[q]
    def observe(state):
        nonlocal last
        last=(state.q,state.direction,tuple(state.left),tuple(state.right))
        q=inv[state.q]
        if seen[q]==allowed[q]:return
        kl,kr=(L,R+1)if state.direction==1 else(L+1,R)
        add_languages(q,state.direction,encode_atoms(state.left,kl),encode_atoms(state.right,kr))
    lemmas,blocks=e.prove_blocks(old)
    def unary(event,before):
        oldq,d,left,right=before;q=inv[oldq]
        if seen[q]==allowed[q]:return
        row=event[1];read,write=row[1:3]
        src,dst=(right,left)if d==1 else(left,right)
        # A bulk on an inserted blank cell has length one and no interior.
        ls=lengths(event[2],MAXCAP,domains)
        if max(ls)<2:return
        assert src[0][0]=='run'
        src_context=encode_atoms(src[1:],K);dst_context=encode_atoms(dst,K)
        signature=(q,d,read,write,ls,src_context,dst_context)
        if signature in bulkseen:return
        bulkseen.add(signature)
        # Saturation at2K preserves every pair of K-cell truncated lengths.
        for n in ls:
            for j in range(1,n):
                s=(('run',read,(n-j,)),)+src_context
                t=(('run',write,(j,)),)+dst_context
                le,ri=(t,s)if d==1 else(s,t)
                add_languages(q,d,le,ri)
    def list_interiors(event,before):
        oldq,d,left,right=before
        src,dst=(right,left)if d==1 else(left,right);atom=src[0]
        assert atom[0]=='list'
        family,reverse_flag=atom[1],atom[3];after=lemmas[oldq,d,family,reverse_flag]
        source_context=encode_atoms(src[1:],K);dest_context=encode_atoms(dst,K)
        sig=(oldq,d,family,reverse_flag,source_context,dest_context)
        if sig in listseen:return
        listseen.add(sig)
        # Split the source list into processed prefix, current arbitrary
        # element and unprocessed suffix. This covers every interior step.
        block=e.block(e.var(11),family)
        if reverse_flag:block=e.rev(block)
        src2=block+[('list',family,'unprocessed',reverse_flag)]+list(src[1:])
        dst2=[('list',after,'processed',not reverse_flag)]+list(dst)
        st=e.State(oldq,dst2,src2,d)if d==1 else e.State(oldq,src2,dst2,d)
        clock=motion=e.ZERO
        for count in range(50):
            st.key();front=st.right if st.direction==1 else st.left
            if count and st.q==oldq and st.direction==d and front[0][0]=='list'and front[0][2]=='unprocessed':break
            observe(st);prev=last
            clock,motion,ev=st.step(old,{},clock,motion)
            if ev[0]=='unary':unary(ev,prev)
            assert ev[0]!='list'
        else:raise AssertionError(('list interior schema failed',sig))
    def bulk(event):
        before=last
        if event[0]=='unary':unary(event,before)
        else:list_interiors(event,before)
    count=steps=0;rows=set()
    for i,site in enumerate(sites):
        masks=info['facts'][i]
        if masks is None:continue
        for pos in((False,True)if site[1]=='CD'else(False,)):
            values=initial_values(site,pos,masks,info['cutoff'],info['modulus'])
            if values is None:continue
            domains=domains_for(site,pos,masks,info['cutoff'],info['modulus'],MAXCAP)
            try:n,rr=restricted_case(old,lemmas,site,pos,values,observe,bulk)
            except Exception as exc:raise RuntimeError((i,site,pos,exc))from exc
            count+=1;steps+=n;rows|=rr
        if count and count%500<2:print('PROGRESS',i,count,steps,len(observed),len(bulkseen),len(listseen),'secs',time.monotonic()-tic,flush=True)
        if a.limit and count>=a.limit:break
    boot=json.loads((basis/'startup.json').read_text());q=start;head=0;ones=set()
    for step in range(boot['steps']+1):
        mask=sum(1<<(k+L)for k in range(-L,R+1)if head+k in ones);seen[q]|=1<<mask
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
    rec=dict(status='SEED_RESTRICTED_SYMBOLIC_RUNTIME_PROJECTION_DISCOVERY',cases=count,symbolic_steps=steps,rows=len(rows),contexts=sum(x.bit_count()for x in seen.values()),state_contexts={q:x.bit_count()for q,x in seen.items()},L=L,R=R,seconds=time.monotonic()-tic,language_projections=len(observed),unary_interiors=len(bulkseen),list_interiors=len(listseen),prefix_cache=list(language.cache_info()),source_sha256=info['source_sha256'],table_sha256=hashlib.sha256((basis/'simplified.tm').read_bytes()).hexdigest(),window_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),boot_steps=boot['steps'],scope='Discovery only. Includes projections of every literal trace state, unary scan interiors and arbitrary finite-list traversal interiors. Register bucket domains refine finite prefixes; domains beyond the projection radius are saturated. Proposed folds require fresh complete runtime and boot proofs.')
    c.dump(a.output.with_suffix('.json'),rec);print(json.dumps({k:z for k,z in rec.items()if k!='state_contexts'},indent=2),flush=True)
if __name__=='__main__':main()
