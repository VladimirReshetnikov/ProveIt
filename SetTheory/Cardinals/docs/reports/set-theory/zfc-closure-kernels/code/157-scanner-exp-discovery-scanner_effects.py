"""Portable finite discovery replay; see README.md for scope and inputs."""
from pathlib import Path
import sys,json,collections
ROOT=Path(__file__).resolve().parents[2]
if len(sys.argv)>2:raise SystemExit('usage: '+Path(__file__).name+' [fresh-output-directory]')
OUT=Path(sys.argv[1]) if len(sys.argv)==2 else ROOT/'experiments/replay'/Path(__file__).stem
OUT.mkdir(parents=True,exist_ok=False)
sys.path.insert(0,str(ROOT/'vendor/runtime'))
import independent_runtime as r
BASE=ROOT/'inputs'
T=r.table(BASE/'primary218.native.tm');S=json.loads((BASE/'primary-sites.json').read_text())
U={k:v for k,v in T.items()if k[0]!=50};U[34,0]=(0,-1,75)
def run(site,positive=False,limit=5000):
    regs=[0]*9
    if positive:regs[site[2]]=1
    ones=r.frame(site[0],regs,[0]);q=84;h=0
    want=r.expected(site,regs,[0])
    for tick in range(limit):
        if tick and (q==254 or (q==84 and r.clean_dispatch(96,h,ones))):
            ok=(q==254) if want is None else q==84 and(h,ones)==want[0][1:]
            if ok:return None
            onepc=[p for p in ones if h<=p<h+52]
            pc=''.join(str(int(p in ones))for p in range(h,max(onepc)+1)) if onepc else ''
            expectedpc=want[1]['pc']if want else None
            tailok=want is not None and {p for p in ones if p>=52}=={p for p in want[0][2]if p>=52}
            return dict(site=site,positive=positive,actual_pc=pc,expected_pc=expectedpc,head=h,steps=tick,register_frame_unchanged=tailok)
        if (q,int(h in ones))not in U:return dict(site=site,error='undefined')
        w,d,q=U[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    return dict(site=site,error='limit')
out=[]
for i,x in enumerate(S):
    for p in ((False,True)if x[1]=='CD'else(False,)):
        z=run(x,p)
        if z:out.append(dict(ordinal=i,**z))
(OUT/'scanner_effects.json').write_text(json.dumps(out,indent=2)+'\n')
print('failures',len(out));print(collections.Counter((x['site'][1],x.get('positive'),x.get('register_frame_unchanged'))for x in out));print(json.dumps(out[:8],indent=2))
