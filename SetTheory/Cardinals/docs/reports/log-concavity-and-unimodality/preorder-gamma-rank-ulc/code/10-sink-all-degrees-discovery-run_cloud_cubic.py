import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,time,sys
import core_kernel as K
from precise_sos import certify
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'all-cloud-cubic';OUT.mkdir(exist_ok=True)
R=K.cores();selected=list(map(int,sys.argv[1:]))if len(sys.argv)>1 else range(len(R));start=time.time();failed=[];done=0
for i in selected:
 if (OUT/f'certificate_{i}.json').exists():continue
 print('START',i,R[i],flush=True);g,_=K.reduced(R[i]);p=K.plus(K.mul(g[1],g[1]),K.scale(K.mul(g[0],g[2]),-2));out=certify(p,[tuple(range(10))],iterations=90)
 if out is None:failed.append(i);print('FAILED',i,flush=True)
 else:
  (OUT/f'certificate_{i}.json').write_text(json.dumps({'rows':R[i],'scaled_gap':'4*(gamma2^2-3 gamma1 gamma3) at maximal E3 cone','terms':out},indent=2)+'\n');done+=1;print('CERTIFIED',i,'terms',len(out),'elapsed',round(time.time()-start,2),flush=True)
print('FINISHED',done,'failed',failed,'seconds',time.time()-start,flush=True)
(ROOT/'cloud_cubic_status.json').write_text(json.dumps({'new_certified':done,'failed':failed,'seconds':time.time()-start}))
