#!/usr/bin/env python3
"""Search physical rotations for the other 68-rule transported words."""
import sys,json,collections,time,itertools,random
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/optimize196'))
sys.path.insert(0,'research_ipra/newsearch')
import rotation_search as rs
from layout import *
OUT=Path(__file__).resolve().parent/'variant_rotations';OUT.mkdir(exist_ok=True)
CAT={tuple(k):{tuple(a) for a in aa} for k,aa in json.loads(Path('research_ipra/newsearch/leaf_actions.json').read_text())}
def expand_program(ax):
    ns=raw_nodes()
    def ex(s):
        if isinstance(s,str):return ex(ax) if s=='x67' else tuple(ex(x) for x in ns[s])
        if isnode(s):return tuple(ex(x) for x in s)
        return s
    return ex('node172')
def leaflist(t):
    out=[]
    def rec(t,p):
        if not isnode(t):out.append((p,t[1],t[2]));return
        rec(t[0],p+(0,));rec(t[1],p+(1,))
    rec(t,());return out
def decode_bad(rows,t,cap=10000):
    bad=[]
    for i,(p,op,arg) in enumerate(leaflist(t)):
        q,h=84,0
        for _ in range(500):
            if not 0<=h<len(p):bad.append(i);break
            b=p[h];a=rows[q,b]
            if h==len(p)-1 and a in CAT.get((op,arg,b),()):break
            if a[0]!=b or a[1] and h==len(p)-1:bad.append(i);break
            q=a[2];h+=1 if a[1] else -1
        else:bad.append(i)
        if len(bad)>=cap:break
    return bad
def scan_ok(t):
    def rec(t,z=0):
        if z>6:return False
        if not isnode(t):return True
        return rec(t[0],z+1) and rec(t[1],0)
    return rec(t)
def initial_folds(rows,shape,goal):
    seen=set()
    def rec(rr,ss,hist):
        if len(hist)==goal:return rr,hist
        ops=opportunities_fast(rr,ss)
        if len(hist)+len(max_matching(ops))<goal:return
        for a,b,opts in ops:
            for acts in itertools.product(*opts):
                nr=fold(rr,a,b,acts);ns=dict(ss);ns.pop(a);key=tuple(sorted(nr))
                if key in seen:continue
                seen.add(key)
                found=rec(nr,ns,hist+[(a,b,acts)])
                if found:return found
    return rec(rows,shape,[])
def export(name,rows,t,hist,ans):
    sites,cs=rs.contract_list(t)
    (OUT/(name+'.json')).write_text(json.dumps({'rows':[[q,b,*v]for(q,b),v in sorted(rows.items())],'sites':sites,'history':hist,'validation':ans}))
start=time.time();receipts=[]
ids=[int(x) for x in sys.argv[1:]] or [6,2,3,4,7,8,9,5,10,11]
for idx in ids:
    path=BASE/'work/optimize196'/f'transport_candidates_local_{idx}.json'
    ax=read_grammar(path);rows,index,shape=build(ax);t=expand_program(ax)
    goal=len(max_matching(opportunities_fast(rows,shape)));f=initial_folds(rows,shape,goal)
    if f is None:print('NO FOLDS',idx,goal,flush=True);continue
    rows,fhist=f;basecfg=rs.cfg(t);bad=decode_bad(rows,t)
    print('VARIANT',idx,'states',len(rows)//2,'folds',goal,'decodebad',len(bad),'scanok',scan_ok(t),'time',time.time()-start,flush=True)
    if bad or not scan_ok(t):continue
    sites,cs=rs.contract_list(t);ans=validate(rows,cs);print('BASECHECK',idx,ans,flush=True)
    if not ans['ok']:continue
    queue=[(rows,t,[])];seen={hash(t)};best=(len(rows)//2,0);tested=0;near=[]
    for depth in range(1,6):
        candidates=[]
        for rr,tt,hist in queue:
            for c in rs.cands(rr,tt):
                if c[0]<2000:continue
                r2,t2=rs.rotate(rr,tt,c);key=hash(t2)
                if key in seen:continue
                seen.add(key);tested+=1
                dd=rs.duplicates(r2)
                if dd:r2=rs.merge(r2,dd)
                n=len(r2)//2
                # Keep potential scan repairs for at most one level.
                sk=scan_ok(t2)
                bd=decode_bad(r2,t2,cap=300) if sk else [0]*300
                score=(n,len(bd),not sk)
                if score[:2]<best:
                    best=score[:2];print('BEST',idx,best,'depth',depth,'hist',hist+[c[:3]],'tested',tested,'sec',time.time()-start,flush=True)
                    if n<=196:export(f'near_{idx}_{n}_{len(bd)}',r2,t2,hist+[c[:3]],{'decodebad':len(bd),'bad_sites':bd})
                if n<196 and not bd and sk:
                    if rs.cfg(t2)!=basecfg:continue
                    sites,cs=rs.contract_list(t2);ans=validate(r2,cs);print('FINALCHECK',idx,n,ans,flush=True)
                    if ans['ok']:export('candidate195',r2,t2,hist+[c[:3]],ans);raise SystemExit()
                if depth<5:candidates.append((score,r2,t2,hist+[c[:3]]))
        candidates.sort(key=lambda x:x[0]);queue=[(rr,tt,hh) for _,rr,tt,hh in candidates[:60]]
        print('DEPTH',idx,depth,'queue',len(queue),'tested',tested,'best',best,'sec',time.time()-start,flush=True)
        if not queue:break
    receipts.append({'variant':idx,'initial_states':len(rows)//2,'best':best,'tested':tested,'seconds':time.time()-start})
    (OUT/'receipt.json').write_text(json.dumps(receipts))
