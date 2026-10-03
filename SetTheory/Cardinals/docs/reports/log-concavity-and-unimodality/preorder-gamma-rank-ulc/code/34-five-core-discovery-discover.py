"""Optional SciPy discovery only. Never used by the proof verifier."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,time
from pathlib import Path
import kernel as K,poly as P
from pair_tools import certify
ROOT=Path(__file__).resolve().parent
OUT=Path(sys.argv[1])if len(sys.argv)>1 else ROOT/'new-candidates'
OUT.mkdir(exist_ok=True);start=time.time()
for i,(code,rows)in enumerate(K.core_list()):
 _,p=P.reduced(rows,strong=False)
 out=[]if min(p.values())>=0 else certify(p)
 if out is None:raise RuntimeError(f'Candidate unresolved at core {i}; this does not refute the theorem')
 (OUT/f'certificate_{i}.json').write_text(json.dumps({'rows':rows,'target':'3G2^2-4G1G3','terms':out},indent=2))
 if i%1000==0:print(i,'exactly accepted candidates',round(time.time()-start,2),'seconds',flush=True)
