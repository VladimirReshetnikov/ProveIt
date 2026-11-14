import sys,json,itertools
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import compiler as c
from build194 import read_table
name=sys.argv[1] if len(sys.argv)>1 else 'primary'
if name not in ('primary','4l','ax11g'):raise ValueError(name)
if name in ('4l','ax11g'):
 packet=HERE/'inputs'
 rows=read_table(packet/f'{name}.native.tm')
 def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
 nodes={k:tup(v) for k,v in json.loads((packet/f'{name}.nodes.json').read_text()).items()}
 c.raw_nodes=lambda:nodes
else:rows=read_table(HERE/'inputs/primary.native.tm')
tree=tup(json.loads((packet/'ax11g.grammar.tree.json').read_text())) if name=='ax11g' else c.read_grammar(HERE/'inputs/primary.grammar.json')
sites,ins,cs=c.source(tree)
R=4
observed={q:set() for q,b in rows}
def bits(seg,n,k):
 out=[]
 for x in seg:
  if x[0]=='b':out.append(x[1])
  elif x[0]=='r':out += [x[1]]*max(0,min(k,x[2]*n+x[3]))
  elif x[0]=='x':
   # A known left delimiter followed by otherwise arbitrary file bits.
   out += [0]+[-1]*(k-1)
  if len(out)>=k:break
 return (out+[0]*k)[:k]
def observe(s):
 q,onl,l,r=s
 if q in c.BOXSTATES:return
 for n in range(R+2):
  L=bits(l,n,R+1);rr=bits(r,n,R+2)
  if not onl:window=list(reversed(L[:R]))+rr[:R+1]
  else:window=list(reversed(L[1:R+1]))+[L[0]]+rr[:R]
  observed[q].add(tuple(window))
print(c.validate(rows,cs,observe=observe))
# Include complete startup observations, including all pre-seed configurations.
ones=set();q=74;head=0
startup_steps=58320 if name=='4l' else 58154
for step in range(startup_steps):
 if q not in c.BOXSTATES:observed[q].add(tuple(int(head+i in ones) for i in range(-R,R+1)))
 w,d,q=rows[q,int(head in ones)]
 (ones.add if w else ones.discard)(head)
 head+=1 if d else -1
# Expand unknowns; symbolic checking is still required after this screen.
contexts={}
for q,ws in observed.items():
 if q in c.BOXSTATES or q==84:continue
 out=set()
 for ws0 in ws:
  unknown=[i for i,x in enumerate(ws0) if x<0]
  for repl in itertools.product((0,1),repeat=len(unknown)):
   w=list(ws0)
   for i,v in zip(unknown,repl):w[i]=v
   out.add(sum(v<<i for i,v in enumerate(w)))
 contexts[q]=sorted(out)
data={'radius':R,'rows':[[q,b,w,int(d),n] for (q,b),(w,d,n) in sorted(rows.items())], 'contexts':contexts}
(HERE/f'{name}_contexts.json').write_text(json.dumps(data))
with (HERE/f'{name}_contexts.txt').open('w') as f:
 print(R,len(data['rows']),file=f)
 for row in data['rows']:print(*row,file=f)
 print(len(contexts),file=f)
 for q,x in contexts.items():print(q,len(x),*x,file=f)
print('contexts',sum(len(x) for x in contexts.values()),'states',len(contexts),'max',max(map(len,contexts.values())))
print('small',[(q,len(ws)) for q,ws in contexts.items() if len(ws)<=4])
