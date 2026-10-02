import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,sys,time,io,contextlib
from concurrent.futures import ProcessPoolExecutor
import kernel as K
import bounded_moment_cubic as B
from precise_sos import certify
R=Path(__file__).parent;OUT=R/'four-sink-moment-cubic'
def one(job):
 i,rows=job;t=time.time();file=OUT/f'certificate_{i}.json'
 if file.exists():return {'id':i,'skip':True}
 p={tuple(B.P.S.unpack(e)):c for e,c in B.P.polynomial(rows).items()};log=io.StringIO()
 with contextlib.redirect_stdout(log):out=certify(p,[tuple(range(12))],iterations=80)
 if out is not None:file.write_text(json.dumps({'rows':rows,'target':'2G2^2-3G1G3 under A=B+C','terms':out},indent=2))
 else:(R/f'failed-precise-{i}.log').write_text(log.getvalue())
 return {'id':i,'pass':out is not None,'squares':len(out)if out is not None else None,'seconds':round(time.time()-t,3)}
if __name__=='__main__':
 limit=int(sys.argv[1])if len(sys.argv)>1 else 9608;workers=int(sys.argv[2])if len(sys.argv)>2 else 4;t=time.time();jobs=[(i,rows)for i,(_,rows)in enumerate(K.core_list()[:limit])if not(OUT/f'certificate_{i}.json').exists()];print('JOBS',len(jobs),'LIMIT',limit,'WORKERS',workers,flush=True);records=[]
 with ProcessPoolExecutor(max_workers=workers)as pool:
  for result in pool.map(one,jobs,chunksize=1):
   records.append(result);print(json.dumps(result),'elapsed',round(time.time()-t,2),flush=True)
 (R/f'parallel-precise-{limit}-status.json').write_text(json.dumps({'records':records,'seconds':time.time()-t},indent=2));print('DONE',len(records),sum(r.get('pass',True)for r in records),flush=True)
