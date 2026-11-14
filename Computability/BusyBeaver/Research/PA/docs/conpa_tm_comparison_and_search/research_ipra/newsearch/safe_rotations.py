from rotation_search import *
OUT=Path(__file__).parent
rows,_=machine();basecfg=cfg(INITIAL);start=time.time();safe=[]
for c in cands(rows,INITIAL):
    if c[0]>=1300:continue
    r,t=rotate(rows,INITIAL,c)
    if cfg(t)!=basecfg:continue
    sites,cs=contract_list(t)
    ans=validate(r,cs)
    print(c[:3],ans,flush=True)
    if ans['ok']:safe.append(c[:3])
(OUT/'safe_rotation_receipt.json').write_text(json.dumps(safe,indent=2))
print('SAFE',safe,flush=True)
queue=[(rows,INITIAL,[])];seen=set()
for depth in range(1,5):
    nxt=[]
    print('DEPTH',depth,'queue',len(queue),'elapsed',time.time()-start,flush=True)
    for rows,t,hist in queue:
        for c in cands(rows,t):
            if c[0]>=1300:continue
            r,tt=rotate(rows,t,c);key=hash(tt)
            if key in seen:continue
            seen.add(key)
            if cfg(tt)!=basecfg:continue
            sites,cs=contract_list(tt)
            ans=validate(r,cs)
            if not ans['ok']:continue
            ds=duplicates(r)
            if ds:r=merge(r,ds)
            paths,byq=interfaces(r,tt);ops=opportunities_fast(r,byq)
            if len(r)//2<196:
                print('SUCCESS DIRECT',hist+[c[:3]],flush=True)
                (OUT/'candidate195.json').write_text(json.dumps({'rows':[[q,b,*v]for(q,b),v in sorted(r.items())],'sites':sites,'rotations':hist+[c[:3]],'duplicates':ds,'validation':validate(r,cs)},indent=2));raise SystemExit()
            for a,b,opts in ops:
                for acts in itertools.product(*opts):
                    rr=fold(r,a,b,acts);check=validate(rr,cs)
                    if check['ok']:
                        print('SUCCESS FOLD',hist+[c[:3]],a,b,acts,flush=True)
                        (OUT/'candidate195.json').write_text(json.dumps({'rows':[[q,bit,*v]for(q,bit),v in sorted(rr.items())],'sites':sites,'rotations':hist+[c[:3]],'fold':[a,b,acts],'validation':check},indent=2));raise SystemExit()
            if depth<4:nxt.append((r,tt,hist+[c[:3]]))
    queue=nxt
