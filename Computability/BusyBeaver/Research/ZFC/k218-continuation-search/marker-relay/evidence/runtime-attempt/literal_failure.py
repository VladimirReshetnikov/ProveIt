from pathlib import Path
import json
P=Path(__file__).resolve().parent
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
def read(p):
 t={}
 for l in p.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,z=l.split();t[int(q),int(b)]=int(w),1 if d=='R'else-1,int(z)
 return t
old=read(REPO/'Computability/BusyBeaver/Research/ZFC/candidate-k218/k218.native.tm')
new=read(P/'relay217.native.tm')
site=json.loads((P/'runtime/runtime.json').read_text())['site'];pc=site[0]
ones={-1,64}|{i for i,b in enumerate(pc)if b=='1'}|{66+2*i for i in range(10)}
cut=[i for i in range(len(pc)-1,-1,-1)if pc[i]=='1'][1];succ=pc[:cut]
want={-1,64}|{i for i,b in enumerate(succ)if b=='1'}|{66+2*i for i in range(10)}
result={'site':site,'registers':[0]*9,'spares':[0],'gap':0,'input_support':sorted(ones),'expected_pc':succ,'expected_support':sorted(want),'runs':{}}
for label,T in [('accepted',old),('relay',new)]:
 O=set(ones);q=84;h=0;trace=[];visits=[]
 for tick in range(20000):
  b=int(h in O);w,d,z=T[q,b]
  if q in(108,10,16,56,122):visits.append([tick,q,h,b,[w,d,z]])
  trace.append([q,h,b,w,d,z]);O.add(h)if w else O.discard(h);q=z;h+=d
  if q in(84,254):break
 result['runs'][label]={'steps':len(trace),'state':q,'head':h,'support':sorted(O),'matches_expected':q==84 and h==0 and O==want,'trace':trace,'selected_visits':visits}
(P/'literal-counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
for name,r in result['runs'].items():print(name,{k:v for k,v in r.items()if k not in('trace','support')})
