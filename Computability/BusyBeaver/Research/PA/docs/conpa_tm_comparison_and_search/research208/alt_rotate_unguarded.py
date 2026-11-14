from pathlib import Path
import sys,json,time
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
def maxzeros(t,run=0):
    if r.leaf(t):return run
    return max(maxzeros(t[0],run+1),maxzeros(t[1],0))
def summary(m,t,hist):
    dd=r.duplicates(m)
    if dd:
        mm=r.merge(m,dd);ss,cs=r.contract_list(t);zero=maxzeros(t)
        if zero>6:return
        ans=r.validate(mm,cs)
        print('candidate',hist,'dups',dd,'states',len(mm)//2,'zero',zero,ans,flush=True)
        data={'rows':[[q,b,*v]for(q,b),v in sorted(mm.items())],'sites':ss,'rotations':hist,'duplicates':dd,'validation':ans}
        if ans['ok']:
            (ROOT/'alternative_candidate195.json').write_text(json.dumps(data,indent=2)+'\n');raise SystemExit()
    return
first=next(c for c in r.cands(m,t) if c[:3]==(2065,2066,1))
m,t=r.rotate(m,t,first)
start=time.time();seen={hash(t)};queue=[(m,t,[first[:3]])];count=0
for depth in range(2,6):
    nxt=[]
    for mi,ti,history in queue:
        ss,_=r.contract_list(ti)
        bad=[p for p,_,_ in ss if '0000000' in ''.join(map(str,p))]
        for c in r.cands(mi,ti):
            if bad and not any(v[:len(p)]==p for p in c[3] for v in bad):continue
            mm,tt=r.rotate(mi,ti,c);hh=hash(tt)
            if hh in seen:continue
            seen.add(hh)
            if r.cfg(tt)!=basecfg:continue
            hist=history+[c[:3]];count+=1
            summary(mm,tt,hist)
            if maxzeros(tt)>6:nxt.append((mm,tt,hist))
    print('DEPTH',depth,'valid',len(nxt),'total',count,'seconds',time.time()-start,flush=True)
    queue=nxt
print('DONE',flush=True)
