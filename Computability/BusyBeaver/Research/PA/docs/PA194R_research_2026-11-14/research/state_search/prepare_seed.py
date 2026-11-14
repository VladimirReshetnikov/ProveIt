#!/usr/bin/env python3
"""Emit the inherited grammar-search input with a chosen fixed native table.

Only controls below1300 are fixed; AX controls are rebuilt from grammar.
With --zero-final, replace the sole breakTo1 leaf by dec6 (entry21).
"""
from pathlib import Path
import argparse,json
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('output',type=Path);p.add_argument('grammars',type=Path,nargs='+');p.add_argument('--zero-final',action='store_true');args=p.parse_args()
rows={}
for ln in args.table.read_text().splitlines():
 q,b,w,d,n=ln.split();q,b,w,n=map(int,(q,b,w,n))
 if q<1300:rows[q,b]=(w,int(d=='R'),n)
controls=sorted({q for q,b in rows});text=[str(len(controls))]+[' '.join(map(str,[q,*rows[q,0],*rows[q,1]]))for q in controls]+[str(len(args.grammars))]
macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,'node60':99,'node61':190}
for k,path in enumerate(args.grammars):
 d=json.loads(path.read_text());rules=d['rules'];values=[];idx={};replaced=0
 def go(t):
  global replaced
  key=json.dumps(t)
  if key in idx:return idx[key]
  if isinstance(t,list):
   if t==['leaf','inc',1]:q=61
   elif t==['leaf','breakTo',1]:q=21 if args.zero_final else -1;replaced+=1
   elif t==['leaf','dec',6]:q=21
   else:raise ValueError(t)
   v=(0,q,-1,-1)
  elif t in rules:
   a,b=rules[t];a,b=go(a),go(b);v=(1,a,b,0)
  else:v=(0,macros[t],-1,-1)
  j=len(values);values.append(v);idx[key]=j;return j
 root=go(d['root']);text.append(f'{k} {len(values)} {root}');text.extend(' '.join(map(str,v))for v in values)
 if args.zero_final:assert replaced==1,(path,replaced)
args.output.write_text('\n'.join(text)+'\n')
print({'fixed_controls':len(controls),'templates':len(args.grammars),'zero_final':args.zero_final})
