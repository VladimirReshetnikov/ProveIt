from pathlib import Path
import sys,json,time,functools,collections
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'support/alternative196'
sys.path.insert(0,str(ROOT.parent/'research_ipra/newsearch'))
import rotation_search as r
m={(int(q),int(b)):(int(w),d=='R',int(t))for line in(BASE/'alternative196.native.tm').read_text().splitlines()for q,b,w,d,t in[line.split()]}
sites=json.loads((BASE/'sites.json').read_text())
leaves={tuple(p):('leaf',op,a)for p,op,a in sites}
def tree(p=()):
    if p in leaves:return leaves[p]
    return tree(p+(0,)),tree(p+(1,))
t=tree();basecfg=r.cfg(t)
nonpure={q for q,b in m if any(m[q,c][:2]!=(c,True) for c in(0,1))}
@functools.lru_cache(None)
def word(t):return (t,) if r.leaf(t) else word(t[0])+word(t[1])
def getguards(mm,tt):
    paths,_=r.interfaces(mm,tt);out=collections.defaultdict(set)
    for q in nonpure:
        for p in paths[q]:
            n=tt
            for b in p:n=n[b]
            out[q,word(n)].add(p[-1] if p else None)
    return out
originalguards=getguards(m,t)
def badguards(mm,tt):
    out=[]
    for key,v in getguards(mm,tt).items():
        if key[0]==2037:continue
        if key in originalguards and not v<=originalguards[key]:out.append(key[0])
    return sorted(set(out))
def maxzeros(t,run=0):
    if r.leaf(t):return run
    return max(maxzeros(t[0],run+1),maxzeros(t[1],0))
def summary(m,t,hist):
    dd=r.duplicates(m)
    if dd:
        mm=r.merge(m,dd);ss,cs=r.contract_list(t);zero=maxzeros(t)
        if zero>6:return
        bad=badguards(mm,t)
        if bad:return
        ans=r.validate(mm,cs)
        print('GUARD CANDIDATE',hist,'dups',dd,'states',len(mm)//2,'zero',zero,ans,flush=True)
        data={'rows':[[q,b,*v]for(q,b),v in sorted(mm.items())],'sites':ss,'rotations':hist,'duplicates':dd,'validation':ans}
        (ROOT/('alt_guard_candidate_'+str(len(hist))+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        if ans['ok']:
            (ROOT/'alternative_candidate195.json').write_text(json.dumps(data,indent=2)+'\n');raise SystemExit()
    return
first=next(c for c in r.cands(m,t) if c[:3]==(2065,2066,1))
m,t=r.rotate(m,t,first)
start=time.time();seen={hash(t)};queue=[(m,t,[first[:3]])];count=0
for depth in range(2,7):
    nxt=[]
    for mi,ti,history in queue:
        ss,_=r.contract_list(ti)
        bad=[p for p,_,_ in ss if '0000000' in ''.join(map(str,p))]
        for c in r.cands(mi,ti):
            if c[0]<2000 or c[1]<2000:continue
            if bad and not any(v[:len(p)]==p for p in c[3] for v in bad):continue
            mm,tt=r.rotate(mi,ti,c);hh=hash(tt)
            if hh in seen:continue
            seen.add(hh)
            if r.cfg(tt)!=basecfg:continue
            hist=history+[c[:3]];count+=1
            summary(mm,tt,hist)
            if maxzeros(tt)>6 and len(badguards(mm,tt))<=2:nxt.append((mm,tt,hist))
    print('DEPTH',depth,'valid',len(nxt),'total',count,'seconds',time.time()-start,flush=True)
    queue=nxt
print('DONE',flush=True)
