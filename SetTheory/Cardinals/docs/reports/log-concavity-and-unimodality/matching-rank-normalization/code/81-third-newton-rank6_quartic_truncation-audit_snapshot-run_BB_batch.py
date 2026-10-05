from concurrent.futures import ProcessPoolExecutor,as_completed
from itertools import product,permutations
from collections import defaultdict
from pathlib import Path
import subprocess,sys,json,time
ROOT=Path(__file__).resolve().parent
perms=list(permutations(range(3)))
def perm(m,p):return sum(1<<p[i] for i in range(3) if m>>i&1)
def canonical(t):return min((min(perm(t[0],p),perm(t[1],p)),max(perm(t[0],p),perm(t[1],p)),perm(t[2],p)) for p in perms)
profiles=sorted({canonical(t) for t in product(range(8),repeat=3)})
def work(group):
 out=[]
 for J,K,H in group:
  file=ROOT/f'BB_certificate_{J}_{K}_{H}_pairs.json'
  if not file.exists():
   with (ROOT/f'batch_{J}_{K}_{H}.log').open('w') as log:
    p=subprocess.run([sys.executable,str(ROOT/'build_BB_certificate.py'),str(J),str(K),str(H),'--fast','--pair-cones'],stdout=log,stderr=subprocess.STDOUT)
   if p.returncode:raise RuntimeError((J,K,H,'process',p.returncode))
  data=json.loads(file.read_text())
  if not data['bad'] and len(data['records'])!=15:raise RuntimeError((J,K,H,'incomplete record'))
  out.append(data);print('barrier' if data['bad'] else 'passed',J,K,H,sum(r['terms'] for r in data['records']),round(data['seconds'],1),flush=True)
 return out
if __name__=='__main__':
 start=time.time();groups=defaultdict(list)
 for t in profiles:groups[t[:2]].append(t)
 results=[]
 with ProcessPoolExecutor(max_workers=3) as pool:
  futures=[pool.submit(work,g) for g in groups.values()]
  for f in as_completed(futures):results+=f.result()
 results.sort(key=lambda x:x['core_columns'])
 manifest={'scope':'Exact primary BB coefficient diagnostic; failed profiles require separate proofs','core_count':len(results),'failed_profiles':[d['core_columns'] for d in results if d['bad']],'basis_instances':sum(len(d['records']) for d in results),'coefficient_entries':sum(r['terms'] for d in results for r in d['records']),'seconds':time.time()-start,'profiles':results}
 (ROOT/'BB_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('COMPLETE',manifest['core_count'],manifest['basis_instances'],manifest['coefficient_entries'],'barriers',manifest['failed_profiles'],flush=True)
