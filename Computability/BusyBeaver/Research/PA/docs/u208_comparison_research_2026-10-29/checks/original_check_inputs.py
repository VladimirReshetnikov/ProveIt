import pathlib,json,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[1]
O=R/'audit'
def need(x,m):
 if not x: raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l.strip() or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in t,'duplicate');need(b in(0,1)and w in(0,1)and d in('L','R'),'alphabet');t[q,b]=(w,1 if d=='R' else -1,z)
 return t
def canonical(t):
 states={q for q,b in t};need(len(states)==208 and len(t)==416,'count');need({z for w,d,z in t.values()}-states=={254},'halt');todo=[0];m={0:0};out=[]
 for q in todo:
  row=[]
  for b in(0,1):
   w,d,z=t[q,b]
   if z==254:r=-1
   else:
    if z not in m:m[z]=len(m);todo.append(z)
    r=m[z]
   row.append((w,d,r))
  out.append(row)
 need(len(m)==208,'reachability');return out,m
def startup(t):
 q=h=0;ones=set()
 for k in range(48140):
  b=int(h in ones);w,d,q=t[q,b];ones.add(h) if w else ones.discard(h);h+=d
 return q,h,sorted(ones)
A=R.parent/'u209_reduction_20261029/release/final/u208_research_2026-10-29_verification.json'
need(sha(A)=='c9eeeb286dc0ac6697b3b5c39b3d676ef73b46365710506c4b315da8f4c43298','owned receipt')
owned=R.parent/'u209_reduction_20261029/table_search'
bases=[]
for name in ('candidate_4564c487','candidate_89145587'):
 p=owned/name/'native.tm';t=table(p);c,m=canonical(t);bases.append((p,t,c,m))
records=[]
for x in json.loads((R/'comparison/comparison.json').read_text())['machines']:
 p=R/x['path'];t=table(p);c,m=canonical(t);matches=[b for b in bases if c==b[2]];need(len(matches)==1,'class');bp,bt,bc,bm=matches[0];inv={v:k for k,v in bm.items()};f={q:inv[i] for q,i in m.items()};f[254]=254
 need(len(f)==209 and f[0]==0,'bijection')
 for (q,b),(w,d,z) in t.items():need(bt[f[q],b]==(w,d,f[z]),'conjugacy')
 # All 48,140 initial steps avoid changed labels; compare represented full tape.
 q,h,ones=startup(t);qq,hh,oo=startup(bt);need((f[q],h,ones)==(qq,hh,oo),'startup')
 records.append(dict(path=str(p.relative_to(R)),native_sha256=sha(p),owned_representative=str(bp.relative_to(R.parent)),bijection=f,transition_identities=416,startup_steps=48140,complete_startup_equal=True))
(O/'input_audit.json').write_text(json.dumps({'status':'PASS','tables':records,'owned_runtime_receipt_sha256':sha(A)},indent=2)+'\n');print('PASS',len(records),'literal tables,',len(records)*416,'conjugacy rows; full startup each')
