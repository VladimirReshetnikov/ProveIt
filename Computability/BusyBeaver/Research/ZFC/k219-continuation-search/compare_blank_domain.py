from pathlib import Path
from collections import deque
import argparse,hashlib,importlib.util,json,time
ap=argparse.ArgumentParser(description='Compare universal and blank-seeded radius7 inductive domains.')
ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
P=args.output.resolve();P.mkdir(parents=True,exist_ok=False)
BASE=Path(__file__).resolve().parent.parent
CHECKER=BASE/'candidate-k219/variant-row157/check_joint_fold.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(CHECKER)=='82d0b364dfdbc7433a58c3c3e7166ec6a32ac9268e0e516f5f113f1287f44031'
spec=importlib.util.spec_from_file_location('original_domain_checker',CHECKER)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def blank_domain(table,start,radius):
 width=2*radius+1;mask=(1<<width)-1
 states={q for q,b in table}|{254};domain={q:set() for q in states}
 domain[start].add(0);todo=deque([(start,0)])
 def post(q,word):
  w,d,z=table[q,(word>>radius)&1]
  written=(word&~(1<<radius))|(w<<radius)
  low=written>>1 if d==1 else (written<<1)&mask
  return z,(low,low|(1<<(width-1) if d==1 else 1))
 while todo:
  q,word=todo.popleft()
  if q==254:continue
  z,words=post(q,word)
  for new in words:
   if new not in domain[z]:domain[z].add(new);todo.append((z,new))
 for q in states-{254}:
  for word in domain[q]:
   z,words=post(q,word)
   assert all(new in domain[z] for new in words)
 assert 0 in domain[start]
 return domain
started=time.monotonic();results=[]
for name,path,pin in [('baseline',BASE/'candidate-k219/k219.native.tm','b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'),('row157',BASE/'candidate-k219/variant-row157/k219-row157.native.tm','1da488749f7f3094f26e5511013505f9440ae613b73f2aa80dcd0a100def5804')]:
 assert sha(path)==pin
 table,start=m.read(path)
 universal=m.domain(table,start,7);blank=blank_domain(table,start,7)
 assert set(universal)==set(blank)
 states=[];changed_rows=[]
 for q in sorted(universal):
  assert blank[q]<=universal[q]
  states.append({'state':q,'all_initial_tapes':len(universal[q]),'blank_seed':len(blank[q]),'removed':len(universal[q]-blank[q])})
  for bit in (0,1):
   old=sum((w>>7)&1==bit for w in universal[q]);new=sum((w>>7)&1==bit for w in blank[q])
   if old!=new:changed_rows.append({'row':[q,bit],'all_initial_tapes':old,'blank_seed':new,'removed':old-new})
 results.append({'seed':name,'table_sha256':pin,'all_contexts':sum(map(len,universal.values())),'blank_contexts':sum(map(len,blank.values())),'identical':universal==blank,'states':states,'changed_rows':changed_rows})
 assert sha(path)==pin
record={'status':'BLANK_SEEDED_INDUCTIVE_DOMAIN_COMPARISON_PASS','seconds':time.monotonic()-started,'radius':7,'source_sha256':sha(Path(__file__)),'checker_sha256':sha(CHECKER),'seeds':results,'scope':'Blank seed is only state0/window0; each shifted-in exterior bit is arbitrary. Closure is independently checked inductive and contained in the all-initial-tape domain. This overapproximates blank execution (and any initial tape with zero central15cells), not all initial tapes. No candidate replay or halting certificate.'}
(P/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'seconds':record['seconds'],'seeds':[{k:v for k,v in r.items() if k not in ('states','changed_rows')}|{'changed_rows':len(r['changed_rows'])} for r in results]},indent=2))
