#!/usr/bin/env python3
"""Bounded discovery of graph-shaped JSON; never a degree or completeness proof."""
from pathlib import Path
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];hits=[]
for f in (D/'research').glob('**/*.json'):
 try:
  j=json.loads(f.read_bytes());w=j.get('witnesses');rows=j.get('source')
  if not isinstance(w,list) or not isinstance(rows,list) or len(w)>33 or len(rows)>164 or not all(isinstance(x,list) and len(x)==4 for x in rows):continue
  d={x:1 for x in w};d.update({x:0 for x in j.get('fixed_numerals',[])})
  for name,op,a,b in rows:
   if op not in ('+','-','*'):raise ValueError('unknown operation')
   da=0 if isinstance(a,int) else d[a];db=0 if isinstance(b,int) else d[b]
   d[name]=da+db if op=='*' else max(da,db)
  degree=d[j['output']]
  if degree<=8:hits.append((len(w),len(rows),degree,str(f.relative_to(D))))
 except (ValueError,KeyError,TypeError,AttributeError,OverflowError,IndexError):pass
for n,o,d,path in sorted(hits):print(n,o,d,path)
