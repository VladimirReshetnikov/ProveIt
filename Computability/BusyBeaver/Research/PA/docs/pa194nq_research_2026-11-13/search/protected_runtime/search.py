import sys,json,itertools,time,traceback
from pathlib import Path
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'reference'))
import symbolic_runtime as s
import independent_runtime as r
s.HEADER_BASE=48
import inspect
exec(inspect.getsource(s.case).replace('range(4000)','range(700)'),s.__dict__)
raw={}
for ln in (P/'input/machine.native.tm').read_text().splitlines():
 q,b,w,d,t=ln.split();raw[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
mapping={int(k):v for k,v in json.loads((P/'reference/legacy_mapping.json').read_text()).items()}
for q,b in raw:mapping.setdefault(q,q+10000)
mapping[254]=254
rows={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in raw.items()}
prot={mapping[q]for q in {0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}}
source=json.loads((P/'input/source.json').read_text())
opcode={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
sites=[[''.join(map(str,p)),opcode[op],arg]for p,op,arg in source['sites']]
cs=[(i,st,pos)for i,st in enumerate(sites)for pos in ([False,True]if st[1]=='CD' else[False])]
seen={};representative=[]
for c in cs:
 key=(c[1][1],c[1][2],c[2])
 if key not in seen:representative.append(c);seen[key]=c[0]
print('reps',len(representative),flush=True)
# Re-derive same generic list traversals with quotient-normalized entry/exit labels.
def prove(table,alias):
 signatures=[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')]
 lemmas={};v=s.var(2)
 for q,d,before,after in signatures:
  q=alias.get(q,q);L=('opaque','left');R=('opaque','right')
  if d==1:
   st=s.State(q,[L],s.block(v,before)+[R]);target=s.State(q,s.rev(s.block(v,after))+[L],[R])
  else:
   st=s.State(q,s.rev(s.block(v,before))+[L],[R],-1);target=s.State(q,[L],s.block(v,after)+[R],-1)
  clock=s.ZERO;motion=s.ZERO
  for _ in range(50):
   if st.key()==target.key():break
   clock,motion,_=st.step(table,{},clock,motion)
  else:raise AssertionError('block failed')
  assert clock==s.add(v,s.num(2)) and motion==(clock if d==1 else s.neg(clock))
  lemmas[q,d,before,d==-1]=after
 return lemmas

states=sorted({q for q,b in rows});non=sorted(set(states)-prot)
mode=sys.argv[1]if len(sys.argv)>1 else'pp'
pairs=list(itertools.combinations(sorted(prot),2)) if mode=='pp' else [(a,b)for a in non for b in sorted(prot)]
pass_blocks=pass_reps=0;cnt=0;start=time.time();surv=[];fails={}
for a,b in pairs:
 if a==96 or b==96:continue
 for pick in itertools.product((a,b),repeat=2):
  if mode!='pp' and pick==(b,b):continue # tested in earlier all-pair search
  cnt+=1;alias={a:b}
  table={(q,bit):(w,d,b if t==a else t)for(q,bit),(w,d,t)in rows.items()if q!=a}
  for bit in(0,1):
   w,d,t=rows[pick[bit],bit];table[b,bit]=(w,d,b if t==a else t)
  try:
   lemmas=prove(table,alias);pass_blocks+=1
   for i,site,pos in representative:s.case(table,lemmas,site,pos)
   pass_reps+=1
   print('PASS reps',a,b,pick,flush=True)
   for i,site,pos in cs:s.case(table,lemmas,site,pos)
   print('SURVIVOR',a,b,pick,flush=True);surv.append([a,b,pick])
  except (AssertionError,KeyError)as e:
   typ=str(e.args[0])[:100];fails[typ]=fails.get(typ,0)+1
  if cnt%100==0:print('progress',cnt,'blocks',pass_blocks,'reps',pass_reps,'secs',round(time.time()-start,2),flush=True)
result={'mode':mode,'candidates':cnt,'pass_blocks':pass_blocks,'pass_representatives':pass_reps,'survivors':surv,'seconds':time.time()-start,'failures':fails}
(P/'results'/('protected_'+mode+'.json')).write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k!='failures'},indent=2),flush=True)
