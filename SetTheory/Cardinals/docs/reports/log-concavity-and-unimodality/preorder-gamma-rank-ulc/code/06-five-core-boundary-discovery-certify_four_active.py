import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,time
import kernel as K,poly as P
from pair_tools import certify
R=Path(__file__).parent;outdir=R/'four-active-cubic';outdir.mkdir(exist_ok=True);t=time.time();recs=[];rowslist=[(int(v[0]),tuple(map(int,v[1:])))for v in [l.split()for l in (R/'four_active_cores.txt').read_text().splitlines()]]
for i,(code,rows)in enumerate(rowslist):
 file=outdir/f'certificate_{i}.json'
 if file.exists():continue
 gs,_=P.reduced(rows);gs=[{e:c for e,c in g.items()if e[4]==0}for g in gs];p=P.plus(P.scale(P.mul(gs[1],gs[1]),2),P.scale(P.mul(gs[0],gs[2]),-3));out=[]if min(p.values())>=0 else certify(p)
 rec={'id':i,'rows':rows,'preorder':K.is_preorder(rows),'passed':out is not None};recs.append(rec)
 if out is not None:file.write_text(json.dumps({'rows':rows,'zero_tail_indices':[4],'target':'2G2^2-3G1G3','terms':out},indent=2))
 else:print('UNRESOLVED',i,flush=True)
 if i%100==0:print(i,'passed',sum(r['passed']for r in recs),'unresolved',sum(not r['passed']for r in recs),'seconds',round(time.time()-t,2),flush=True)
(R/'four-active-cubic-status.json').write_text(json.dumps({'records':recs,'seconds':time.time()-t},indent=2));print('DONE',len(recs),sum(r['passed']for r in recs),flush=True)
