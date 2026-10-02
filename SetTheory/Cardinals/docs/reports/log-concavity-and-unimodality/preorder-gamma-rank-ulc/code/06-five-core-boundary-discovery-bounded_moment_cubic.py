import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,time,sys
import kernel as K
import packed_cubic as P
P.E={0:[(0,1)],1:[(P.SH[10],1),(P.SH[11],2)],2:[(P.SH[10]+P.SH[11],2),(2*P.SH[11],3)],3:[(P.SH[10]+2*P.SH[11],3),(3*P.SH[11],4)]}
if __name__=='__main__':
 R=Path(__file__).parent;outdir=R/'four-sink-moment-cubic';outdir.mkdir(exist_ok=True);t=time.time();recs=[];end=int(sys.argv[1])if len(sys.argv)>1 else 9608
 for i,(code,rows)in enumerate(K.core_list()[:end]):
  
  if len(sys.argv)>2 and i<int(sys.argv[2]):continue
  file=outdir/f'certificate_{i}.json'
  if file.exists():continue
  p=P.polynomial(rows);out=[]if min(p.values())>=0 else P.S.certify(p)
  rec={'id':i,'rows':rows,'preorder':K.is_preorder(rows),'passed':out is not None};recs.append(rec)
  if out is not None:file.write_text(json.dumps({'rows':rows,'target':'2G2^2-3G1G3 under A=B+C','terms':out},indent=2))
  else:print('UNRESOLVED',i,flush=True)
  if i%100==0:print(i,'passed',sum(r['passed']for r in recs),'unresolved',sum(not r['passed']for r in recs),'seconds',round(time.time()-t,2),flush=True)
 (R/'four-sink-moment-cubic-status.json').write_text(json.dumps({'records':recs,'seconds':time.time()-t},indent=2));print('DONE',len(recs),sum(r['passed']for r in recs),flush=True)
