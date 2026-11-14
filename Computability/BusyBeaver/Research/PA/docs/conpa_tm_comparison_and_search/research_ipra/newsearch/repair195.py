from rotation_search import *
rows,_=machine();basecfg=cfg(INITIAL)
c=next(c for c in cands(rows,INITIAL) if c[:3]==(1362,1361,1))
r,t=rotate(rows,INITIAL,c)
def max0(t):
    ans=0
    def go(t,n):
        nonlocal ans
        ans=max(ans,n)
        if not leaf(t):go(t[0],n+1);go(t[1],0)
    go(t,0);return ans
first=[r,t,[c[:3]]]
queue=[first];seen=set();start=time.time()
for depth in range(1,5):
    nxt=[]
    print('DEPTH',depth,'queue',len(queue),flush=True)
    for r,t,hist in queue:
        for c in cands(r,t):
            rr,tt=rotate(r,t,c)
            hh=hash(tt)
            if hh in seen:continue
            seen.add(hh)
            if cfg(tt)!=basecfg:continue
            dd=duplicates(rr)
            if not dd:continue
            mh=max0(tt)
            if mh<=6:
                mm=merge(rr,dd);sites,cs=contract_list(tt)
                ans=validate(mm,cs)
                print('SCAN GOOD',hist+[c[:3]],'dups',dd,'check',ans,flush=True)
                if ans['ok']:
                    Path(__file__).with_name('candidate195.json').write_text(json.dumps({'rows':[[q,b,*v] for (q,b),v in sorted(mm.items())],'sites':sites,'rotations':hist+[c[:3]],'duplicate_merge':dd,'validation':ans},indent=2));raise SystemExit()
            elif depth<4:nxt.append([rr,tt,hist+[c[:3]]])
    queue=nxt
    print('ELAPSED',time.time()-start,flush=True)
