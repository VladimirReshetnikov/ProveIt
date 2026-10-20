#!/usr/bin/env python3
"""Reassociate open source chunks, checking the entire guarded source graph.

Only row-preserving outer leaves are moved. The middle child must have a
literal bit-preserving right-moving entry, so changing its branch label is
unambiguous at the table level. Source graph equality is checked separately.
Every proposed smaller table still requires complete runtime and boot proofs.
"""
from simplify import *


def moves(t,lr,clones=False):
    qs=collect(lr);ports=collections.Counter(z for w,d,z in t.values());out=[];pairq=collections.defaultdict(list)
    for s,ns in qs.items():
        if len(ns)==1:
            n=next(iter(ns));pairq[n[1],n[2]].append(s)
    fresh=next(q for q in range(230,254)if(q,0)not in t)
    for q,ns in qs.items():
        if len(ns)!=1:continue
        n=next(iter(ns))
        for bit in(0,1):
            if t[q,bit][:2]!=(bit,1):continue
            r=t[q,bit][2]
            if r not in qs or len(qs[r])!=1 or ll(n[bit+1])or r!=n[bit+1][0]:continue
            ch=n[bit+1];a,b,cc=(ch[1],ch[2],n[2])if bit==0 else(n[1],ch[1],ch[2])
            # Only the middle atom crosses from a right edge to a left edge.
            midbit=1-bit
            if t[r,midbit][:2]!=(midbit,1):continue
            pair=(b,cc)if bit==0 else(a,b)
            if ports[r]==1:out.append((q,r,bit,r,'rewrite'))
            for s in pairq.get(pair,[]):
                if s not in(q,r):out.append((q,r,bit,s,'reuse'))
            if clones and ports[r]>1:out.append((q,r,bit,fresh,'clone'))
    return out


def perform(t,lr,rot):
    q,r,bit,s,kind=rot;n=next(iter(collect(lr)[q]));ch=n[bit+1];tt=t.copy()
    if bit==0:
        a,b,cc=ch[1],ch[2],n[2];nn=(q,a,(s,b,cc));tt[q,0]=t[r,0];tt[q,1]=(1,1,s)
        if kind!='reuse':tt[s,0]=(0,1,t[r,1][2]);tt[s,1]=t[q,1]
    else:
        a,b,cc=n[1],ch[1],ch[2];nn=(q,(s,a,b),cc);tt[q,0]=(0,1,s);tt[q,1]=t[r,1]
        if kind!='reuse':tt[s,0]=t[q,0];tt[s,1]=(1,1,t[r,0][2])
    @c.cache
    def change(node):return nn if node==n else node if ll(node)else(node[0],change(node[1]),change(node[2]))
    return tt,change(lr)


def probe_folds(tt,lr):
    tt,lr,gc=gc_quotient(tt,lr);nn,hist=simplify(tt)
    if nn!=tt:
        def phi(q):
            for h in hist:
                if q==h['drop']:q=h['keep']
            return q
        @c.cache
        def rename(n):return n if ll(n)else(phi(n[0]),rename(n[1]),rename(n[2]))
        lr=rename(lr);tt=nn
    hits,score=folds(tt)
    for drop,keep,h0,h1 in hits:
        u={(q,b):(w,d,keep if z==drop else z)for(q,b),(w,d,z)in tt.items()if q!=drop};u[keep,0]=(0,-1,h0);u[keep,1]=(1,-1,h1)
        proof=v.prove(tt,u,0,0,keep,drop,0,None,8,65,20000)
        if not proof['status'].startswith('PASS'):continue
        @c.cache
        def alias(n):return n if ll(n)else(keep if n[0]==drop else n[0],alias(n[1]),alias(n[2]))
        tt,lr=u,alias(lr);hist.append(dict(fold=[drop,keep,h0,h1],proof=proof));break
    return tt,lr,dict(gc=gc,folds=hist,score=score)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--basis',type=Path);ap.add_argument('--clones',action='store_true');ap.add_argument('--iterations',type=int,default=0);ap.add_argument('--seed',type=int,default=621);ap.add_argument('--output',type=Path,default=Path(__file__).parent/'open_rotations');a=ap.parse_args()
    if a.basis:tt,_=v.parse_table((a.basis/'candidate225.klabels.tm').read_bytes());r=c.tree(json.loads((a.basis/'sites225.json').read_text()))
    else:tt=t;r=root
    lr=labeled(tt,r);basegraph=c.graph_arithmetic(c.sites(r));out=a.output;out.mkdir(exist_ok=True,parents=True);tic=time.monotonic();counts=collections.Counter();accepted=[];rs=moves(tt,lr,a.clones)
    for i,rot in enumerate(rs):
        uu,lrr=perform(tt,lr,rot);rr=unlabel(lrr)
        try:
            if c.graph_arithmetic(c.sites(rr))!=basegraph:counts['graph_changed']+=1;continue
        except Exception:counts['graph_invalid']+=1;continue
        counts['graph_equal']+=1
        bad=bad_mapping(uu,lrr)
        if bad:counts['prefix_invalid']+=1;continue
        metrics=c.metrics(rr)
        if metrics['maximum_zero_run']>6:counts['zero7']+=1;continue
        result,lr2,rec=probe_folds(uu,lrr);rec.update(rotation=rot,states=len(result)//2,metrics=metrics)
        accepted.append(rec);counts['fully_screened']+=1
        print('PASS',i,rot,'states',len(result)//2,'score',rec['score'],'folds',[{k:z for k,z in f.items()if k!='proof'}for f in rec['folds']],flush=True)
        name=f'layout_{i}'
        if len(result)//2<=224 or metrics['maximum_zero_run']<=5:name=f'HIT_{i}'
        (out/(name+'.tm')).write_bytes(encode(result));c.dump(out/(name+'_sites.json'),c.sites(unlabel(lr2)));c.dump(out/(name+'_receipt.json'),rec)
    c.dump(out/'scan.json',dict(moves=len(rs),counts=dict(counts),accepted=accepted,seconds=time.monotonic()-tic));print('DONE',len(rs),dict(counts),'secs',time.monotonic()-tic,flush=True)
if __name__=='__main__':main()
