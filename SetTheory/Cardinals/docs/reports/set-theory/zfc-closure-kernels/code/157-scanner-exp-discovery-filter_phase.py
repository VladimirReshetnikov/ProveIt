"""Portable finite discovery replay; see README.md for scope and inputs."""
from pathlib import Path
import sys,json,time
ROOT=Path(__file__).resolve().parents[2]
if len(sys.argv)>2:raise SystemExit('usage: '+Path(__file__).name+' [fresh-output-directory]')
OUT=Path(sys.argv[1]) if len(sys.argv)==2 else ROOT/'experiments/replay'/Path(__file__).stem
OUT.mkdir(parents=True,exist_ok=False)
sys.path.insert(0,str(ROOT/'vendor/runtime'))
import independent_runtime as r
BASE=ROOT/'inputs'
T=r.table(BASE/'primary218.native.tm');S=json.loads((BASE/'primary-sites.json').read_text())
def test(tab,site,positive=False,limit=5000):
    regs=[0]*9
    if positive:regs[site[2]]=1
    ones=r.frame(site[0],regs,[0]);q=84;h=0
    want=r.expected(site,regs,[0])
    for tick in range(limit):
        if tick and (q==254 or (q==84 and r.clean_dispatch(96,h,ones))):
            return (q==254) if want is None else q==84 and(h,ones)==want[0][1:]
        if (q,int(h in ones))not in tab:return False
        w,d,q=tab[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    return False
cases=[(i,p)for i,x in enumerate(S)for p in ((False,True)if x[1]=='CD'else(False,))]
cases.sort(key=lambda x: (0 if x[0] in [40,41,66,4572,4705,4718,0,1,37,38,39] else 1,x[0]))
hits=[json.loads(x)for x in (ROOT/'experiments/receipts/repair_phase_hits.jsonl').read_text().splitlines()]
receipts=[];start=time.monotonic()
for j,hit in enumerate(hits):
    U={k:v for k,v in T.items()if k[0]!=50};U[34,0]=(0,-1,75);q,b,w,d,z=hit;U[q,b]=(w,d,z)
    checked=0
    for i,p in cases:
        if not test(U,S[i],p):break
        checked+=1
    rec=dict(index=j,patch=hit,checked=checked,failed_at=None if checked==len(cases)else[i,p]);receipts.append(rec)
    print(rec,flush=True)
    if checked==len(cases):
        out=OUT/f'unverified-phase-hit{j}.native.tm'
        out.write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(U.items())))
print('checked',len(hits),'seconds',time.monotonic()-start,'max_pass',max(x['checked']for x in receipts))
(OUT/'phase_filter_results.json').write_text(json.dumps(receipts,indent=2)+'\n')
