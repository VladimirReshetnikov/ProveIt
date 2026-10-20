#!/usr/bin/env python3
"""Search exact-CFG rotations, allowing open middle chunks and one-sided exits.

For ((A,B),C) <-> (A,(B,C)), it suffices that A has no escaping
break and C no escaping continue. B may have either kind of exit.
Each accepted complete source is independently checked by both CFG resolvers.
All tables still need the universal instruction certificate before promotion.
"""
from pathlib import Path
import sys, collections, argparse, random, hashlib, json, time, math
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'machine-search'))
import table_layout as m
c,sr=m.c,m.sr

def candidates(root,T):
    groups,paths=sr.decoder_map(c,T,root)
    inv=collections.defaultdict(list)
    for q,ns in groups.items():
        for n in ns: inv[n].append(q)
    incoming=collections.Counter(v[2] for v in T.values())
    for q,ns in groups.items():
        if len(ns)!=1 or any(T[q,b][:2]!=(b,1) for b in (0,1)): continue
        x=next(iter(ns))
        for side in (0,1):
            y=x[side]; r=T[q,side][2]
            if c.leaf(y) or groups[r]!={y} or any(T[r,b][:2]!=(b,1) for b in (0,1)): continue
            a,b,d=(*y,x[1]) if side==0 else (x[0],*y)
            if c.boundary(a)[0] or c.boundary(d)[1]: continue
            z=(b,d) if side==0 else (a,b)
            xx=(a,z) if side==0 else (z,d)
            aa,bb,dd=(T[r,0][2],T[r,1][2],T[q,1][2]) if side==0 else (T[q,0][2],T[r,0][2],T[r,1][2])
            ports=list(inv.get(z,[]))
            if not ports:
                if incoming[r]==1 and r not in (0,84): ports=[r]
                else: ports=[next(j for j in range(280,550) if (j,0) not in T)]
            for zz in ports:
                TT=T.copy()
                TT[q,0]=(0,1,aa if side==0 else zz)
                TT[q,1]=(1,1,zz if side==0 else dd)
                if zz not in inv.get(z,[]):
                    TT[zz,0]=(0,1,bb if side==0 else aa)
                    TT[zz,1]=(1,1,dd if side==0 else bb)
                TT=m.prune(TT)
                if len(TT)>452: continue
                rr=sr.replace_all(c,root,x,xx)
                yield rr,TT,{'state':q,'child':r,'side':side,'new_middle':zz,
                    'path':paths[q][0],'source_changed_from':len(c.sites(x)),
                    'boundaries':[c.boundary(n) for n in (a,b,d)],'states':len(TT)//2}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--basis',type=Path,default=Path('work/machine-search/sym224'))
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seconds',type=int,default=300)
    ap.add_argument('--seed',type=int,default=981224)
    args=ap.parse_args();args.output.mkdir(exist_ok=True,parents=True)
    rows0=json.loads((args.basis/'sites.json').read_text())
    root0=c.tree(rows0);T0=sr.read_table(args.basis/'candidate.k.tm')
    graph0,_=c.graph_arithmetic(rows0);assert graph0==c.graph_intervals(rows0)
    rng=random.Random(args.seed);start=time.monotonic()
    best=(len(T0)//2,m.bad(root0),m.stats(root0)[3]); bestT=T0; bestroot=root0;besthist=[]
    seen=set(); attempts=good=cfgfails=mapfails=screenfails=bootfails=0
    def key(t,T):return hashlib.sha256(c.compact(c.sites(t))+sr.encode_table(T)).digest()
    def verify(t,T):
        nonlocal attempts,good,cfgfails,mapfails,screenfails,bootfails
        attempts+=1
        rows=c.sites(t)
        try:
            assert c.graph_arithmetic(rows)[0]==c.graph_intervals(rows)==graph0
        except (ValueError,AssertionError):cfgfails+=1;return False
        try:sr.decoder_map(c,T,t)
        except (ValueError,KeyError):mapfails+=1;return False
        p=args.output/'current.sites'
        p.write_text(''.join(f'{pc} {op} {n if n is not None else -1}\n' for pc,op,n in rows))
        m.FAST.init_cases(str(p).encode()); a=m.arr(T)
        if m.FAST.screen(a,10000):screenfails+=1;return False
        if m.FAST.boot(a)!=1:bootfails+=1;return False
        good+=1;return True
    def save(t,T,hist,name='best'):
        (args.output/(name+'_sites.json')).write_bytes(c.compact(c.sites(t)))
        (args.output/(name+'.k.tm')).write_bytes(sr.encode_table(T))
        (args.output/(name+'.legacy.tm')).write_bytes(sr.encode_table(m.legacy(T),95))
        receipt=dict(status='EXACT_CFG_FINITE_RUNTIME_BOOT_PASS',basis=str(args.basis),
            metrics=[len(T)//2,m.bad(t),m.stats(t)[3]],source_metrics=c.metrics(t),history=hist,
            attempts=attempts,accepted=good,cfgfails=cfgfails,mapfails=mapfails,
            screenfails=screenfails,bootfails=bootfails,seconds=time.monotonic()-start)
        (args.output/(name+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    assert verify(root0,T0);save(root0,T0,[])
    print('INITIAL',best,flush=True)
    walk=0
    while time.monotonic()-start<args.seconds:
        if walk%3==0:root,T,hist=root0,T0,[]
        else:root,T,hist=bestroot,bestT,besthist[:]
        temp=rng.choice((.12,.3,.8,1.5))
        for step in range(70):
            if time.monotonic()-start>=args.seconds:break
            choices=[]
            for rr,TT,h in candidates(root,T):
                kk=key(rr,TT)
                if kk in seen:continue
                met=(len(TT)//2,m.bad(rr),m.stats(rr)[3])
                score=(met[0]-224)*5+met[1]*.1+met[2]*.05+rng.expovariate(1/temp)
                choices.append((score,met,kk,rr,TT,h))
            choices.sort(key=lambda z:z[0]); chosen=None
            for _,met,kk,rr,TT,h in choices:
                seen.add(kk)
                if verify(rr,TT):chosen=(met,rr,TT,h);break
            if chosen is None:break
            met,root,T,h=chosen;hist.append(h)
            if met<best:
                best=met;bestroot=root;bestT=T;besthist=hist[:];save(root,T,hist)
                print('BEST',best,'hist',len(hist),'attempts',attempts,'time',round(time.monotonic()-start,2),flush=True)
            if met[0]<224:
                save(root,T,hist,'smaller');print('SUB224',met,flush=True);return
            if met[0]==224 and met[1]==0:
                save(root,T,hist,'scanner_ready');print('SCANNER_READY',met,flush=True);return
        walk+=1
        print('WALK',walk,'best',best,'attempts',attempts,'accepted',good,'cfgfails',cfgfails,'time',round(time.monotonic()-start,2),flush=True)
    save(bestroot,bestT,besthist)
    print('DONE',best,'attempts',attempts,'accepted',good,'cfgfails',cfgfails,flush=True)

if __name__=='__main__':main()
