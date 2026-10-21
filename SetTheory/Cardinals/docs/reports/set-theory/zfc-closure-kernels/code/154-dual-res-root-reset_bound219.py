#!/usr/bin/env python3
"""Explore exact-CFG source reassociation to shorten the reset marker.

The intended opportunity is max-zero-run five with no larger decoder.
Counts alone never certify the shortened reset scanner.
"""
import control_rotation_fast219 as q
import hashlib,json,time,random,functools,argparse
from pathlib import Path
s=q.s;b=q.b;old=q.old;T=q.T
ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=30);ap.add_argument('--out',default='reset_bound219_pareto');args=ap.parse_args()
OUT=q.ROOT/'root_work'/args.out;OUT.mkdir(exist_ok=True)

def nodes(n):
    seen=set()
    def go(t):
        if t in seen:return
        seen.add(t)
        if not s.leaf(t):go(t[0]);go(t[1])
    go(n);return seen

@functools.lru_cache(6000)
def counts(n,k=0):
    if s.leaf(n):return(int(k>=6),int(k>=5))
    a=counts(n[0],k+1);bb=counts(n[1],0)
    return(a[0]+bb[0],a[1]+bb[1])

q.q.nodes=nodes
front=[(old,[])];seen={hash(old)};rng=random.Random(21850);start=time.time();records=[]
for depth in range(args.rounds):
    choices=[];local_seen=set();mini=999
    for tr,chain in front:
        for x in nodes(tr):
            if s.leaf(x):continue
            for direction in (0,1):
                for mode in (0,1):
                    h=q.rotated(x,direction,mode)
                    if h is None:continue
                    y,changes=h
                    new=q.q.replace_all(tr,x,y);hh=hash(new)
                    if hh in seen or hh in local_seen:continue
                    local_seen.add(hh)
                    nn=len(nodes(new));z=q.info(new)[1]
                    if nn>209 or z>6:continue
                    v=counts(new)[0]
                    ch=chain+[{'direction':direction,'source_subtree':x,'changes':changes}]
                    # Spend at most three source nodes in eliminating the long suffixes.
                    score=nn+v/38*2
                    choices.append((score,nn,v,rng.random(),new,ch))
                    if z<=5 and nn<=208:
                        rr=s.sites(new)
                        assert s.graph_intervals(rr)==q.G and s.graph_arithmetic(rr)[0]==q.G
                        key=hashlib.sha256(s.compact(rr)).hexdigest()[:16]
                        d=OUT/key;d.mkdir(exist_ok=True)
                        (d/'sites.json').write_bytes(s.compact(rr))
                        rec={'key':key,'metrics':s.metrics(new),'chain':ch,'scope':'EXACT_SOURCE_CFG_ONLY'}
                        try:
                            U,m=q.q.compiler.compile_tree(T,old,new,extend_direct=True)
                            rec['compiler']=m;(d/'candidate.tm').write_bytes(b.table_bytes(U))
                        except Exception as e:rec['compiler_error']=repr(e)
                        (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');records.append({k:v for k,v in rec.items()if k!='chain'})
                        print('HIT',json.dumps(records[-1]),flush=True)
    seen.update(local_seen);choices.sort(key=lambda x:(x[2],x[3]))
    selected=[]
    for nn in range(204,210):
        selected += [x for x in choices if x[1]==nn][:4]
    front=[(tr,ch)for _,_,_,_,tr,ch in selected]
    checkpoints=[]
    for k,(a,nn,v,_,tr,ch) in enumerate(selected):
        rr=s.sites(tr);name=f'front_{k:02d}'
        (OUT/(name+'.sites.json')).write_bytes(s.compact(rr))
        (OUT/(name+'.chain.json')).write_text(json.dumps(ch)+'\n')
        cm=None
        if depth%5==4:
            try:
                U,cm=q.q.compiler.compile_tree(T,old,tr,extend_direct=True)
                (OUT/(name+'.tm')).write_bytes(b.table_bytes(U))
            except Exception as e:cm={'error':repr(e)}
        checkpoints.append({'name':name,'dag_nodes':nn,'six_zero_leaves':v,'compiler':cm})
    stats={'round':depth+1,'seen_hashes':len(seen),'frontier':[[a,nn,v]for a,nn,v,_,_,_ in selected],'checkpoints':checkpoints,'seconds':time.time()-start,'records':records}
    (OUT/'summary.json').write_text(json.dumps(stats,indent=2)+'\n')
    print('ROUND',depth+1,'SEEN',len(seen),'BEST',stats['frontier'][:4],'SEC',round(stats['seconds'],1),flush=True)
    q.local.cache_clear();q.rotated.cache_clear();q.info.cache_clear();q.q.width.cache_clear();counts.cache_clear()
    if not front:break
