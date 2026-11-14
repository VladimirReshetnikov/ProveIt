from pathlib import Path
import sys,json,hashlib,time
B=Path(sys.argv[1]).resolve();sys.path.insert(0,str(B/'code'))
from check_local import read_table,need
import symbolic_runtime as engine
need(__debug__,'normal Python required')
for n,h in {'symbolic_runtime.py':'61b9c66272e8fd149829177cc384013814aea3c6b3b6b6f48e462d3913ea2022','independent_runtime.py':'d490397a2b31be4f7f62461a3d9bcd88faf9093de904e43eea1b865561e7b7ee'}.items():need(hashlib.sha256((B/'code'/n).read_bytes()).hexdigest()==h,'engine changed')
t=read_table(B/'alternative/u208.native.tm'); sites=json.loads((B/'alternative/sites.json').read_text());m={int(k):int(v) for k,v in json.loads((B/'machine_parent/legacy_mapping.json').read_text()).items()};states={q for q,b in t}
for q in states|{254}:m.setdefault(q,q+1000)
need(len({m[q] for q in states|{254}})==209,'bad relabel')
lit={(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in t.items()}; lemmas,blocks=engine.prove_blocks(lit);used=set();n=steps=0;start=time.monotonic()
for i,s in enumerate(sites):
 for p in ((False,True) if s[1]=='CD' else (False,)):
  c=engine.case(lit,lemmas,s,p);used.update(c['rows']);n+=1;steps+=c['symbolic_steps'];need(len(c['duration'])==13 and c['duration'][0]>0 and all(v>=0 for v in c['duration']),'duration')
 if i%1000==0:print(i,n,flush=True)
for b in blocks:
 for e in b['trace']:used.add(tuple(e[1][:2]))
need(n==5084 and used==set(lit),'coverage')
r={'status':'FRESH_ALTERNATIVE208_RUNTIME_PASS','cases':n,'rows':len(used),'symbolic_inferences':steps,'seconds':time.monotonic()-start,'scope':'ordinary inherited unary/list induction engine, not kernel proof','machine_sha256':hashlib.sha256((B/'alternative/u208.native.tm').read_bytes()).hexdigest()};print(json.dumps(r,indent=2))
