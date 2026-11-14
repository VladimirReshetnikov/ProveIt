from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).parent/'vendor'))
import compiler as c

def read(path):
 r={}
 for line in Path(path).read_text().splitlines():
  q,b,w,d,n=line.split();r[int(q),int(b)]=int(w),d=='R',int(n)
 return r
base=read('runtime193.native.tm');orig=read('pa194.native.tm')
sites,ins,contracts=c.source(c.read_grammar('vendor/grammar.json'))
base[51,0]=orig[51,0]
qs=sorted({q for q,b in base})
# Select clauses reaching either folded native entry on baseline model.
observed=set()
def observe(s):observed.add(s[0])
cover=[]
for contract in contracts:
 observed.clear();c.run(orig,contract,observe=observe)
 if 88 in observed or 301 in observed: cover.append(contract)
print('focused clauses',len(cover),'total',len(contracts),flush=True)
# Latest failures first to speed rejection.
witness=[];accepted=[];t=time.time();attempts=0
for w in (0,1):
 for d in (False,True):
  for target in qs:
   attempts+=1;candidate=dict(base);candidate[88,0]=(w,d,target)
   if any(c.run(candidate,cc) is None for cc in witness):continue
   failure=next((cc for cc in cover if c.run(candidate,cc) is None),None)
   if failure is not None:
    if failure not in witness:witness.insert(0,failure)
    continue
   result=c.validate(candidate,contracts)
   accepted.append({'action':[w,int(d),target],'result':result})
   print(accepted[-1],flush=True)
print(json.dumps({'attempts':attempts,'accepted':accepted,'witness_sites':[(x[0],x[1]) for x in witness],'elapsed':time.time()-t}),flush=True)
