#!/usr/bin/env python3
"""Bind every search template to the three exact bundled source trees."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,'node60':99,'node61':190}
def read_grammar(path):
 x=json.loads(path.read_text());rules=x['rules']
 def go(t):
  if isinstance(t,str):return tuple(map(go,rules[t]))if t in rules else MACROS[t]
  if t==['leaf','inc',1]:return 61
  if t==['leaf','breakTo',1]:return -1
  return tuple(map(go,t))
 return go(x['root'])
for case in json.loads((HERE/'cases.json').read_text()):
 d=HERE/case['name'];data=iter((d/'templates.txt').read_text().split());take=lambda:int(next(data));n=take();assert n==case['fixed_controls'];rows={}
 for i in range(n):
  q=take();assert q not in rows;actions=[]
  for b in (0,1):
   w,move,target=take(),take(),take();assert w in(0,1)and move in(0,1);actions.append((w,move,target))
  rows[q]=actions
 assert take()==3
 for expected in range(3):
  tid,count,root=take(),take(),take();assert tid==expected;values=[]
  for i in range(count):
   op,a,b,c=take(),take(),take(),take();values.append((values[a],values[b])if op else a)
  assert values[root]==read_grammar(d/f'seed{tid}.grammar.json'),(case['name'],tid)
 assert next(data,None)is None
 print(case['name'],': three exact template/source-tree identities PASS')
