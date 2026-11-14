from search_folds import *
import sys,random
rows=read_table(Path(sys.argv[1]) if len(sys.argv)>1 else BASE/'sources/bb196/data/pa196.tm');k=4;reach=reachable(rows,k);n=196
start=time.time();alt={};lens={}

def try_action(q,b,act,v,limit=31):
 tape={i-k:(v>>i)&1 for i in range(2*k+1)};dst=tape.copy()
 ow,od,ot=rows[q,b];dst[0]=ow
 w,d,t=act;tape[0]=w;h=d
 for steps in range(1,limit+1):
  if h==od and t==ot and tape==dst:return steps
  if h not in tape or (t,tape[h]) not in rows:return 0
  w,d,t=rows[t,tape[h]];tape[h]=w;h+=d
 return 0

for q in range(n):
 for b in(0,1):
  vs=sorted(v for v in reach[q] if ((v>>k)&1)==b)
  # Mix both ends to expose near-neighbor variation early.
  vs=vs[::2]+list(reversed(vs[1::2]));opts=[]
  for act in itertools.product((0,1),(-1,1),range(n+1)):
   ls=[]
   for v in vs:
    x=try_action(q,b,act,v)
    if not x:break
    ls.append(x)
   else:opts.append(act);lens[q,b,act]=sorted(set(ls))
  alt[q,b]=set(opts)
 if q%20==0:print('PROGRESS',q,sum(map(len,alt.values())),time.time()-start,flush=True)
hits=[];pairs=0
for a in range(1,n):
 for b in range(a+1,n):
  x0=alt[a,0]&alt[b,0];x1=alt[a,1]&alt[b,1]
  if not x0 or not x1:continue
  pairs+=1;print('PAIR',a,b,x0,x1,flush=True)
  for aa,bb in((a,b),(b,a)):
   for z,o in itertools.product(x0,x1):
    chk=local_check(rows,aa,bb,{(aa,0):z,(aa,1):o},reach,k,limit=35)
    if chk:
     hit={'a':aa,'b':bb,'zero':z,'one':o,'lengths':chk};hits.append(hit);print('HIT',hit,flush=True)
(BASE/('research/alternatives_'+(Path(sys.argv[1]).stem if len(sys.argv)>1 else 'baseline')+'.json')).write_text(json.dumps({'alternatives':{str(k):sorted(v) for k,v in alt.items()},'pairs':pairs,'hits':hits},indent=2))
print('DONE',pairs,len(hits),time.time()-start,flush=True)
