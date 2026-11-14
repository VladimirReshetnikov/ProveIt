#!/usr/bin/env python3
"""Check an exact obstruction to this fixed dictionary, not to all layouts."""
from pathlib import Path
import sys,json
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
import emitter189 as e

def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x

def leading(t):return 0 if e.s.isleaf(t)else 1+leading(t[0])

def token_leading(t):
 return leading(e.s.NODES[t])if isinstance(t,str)else 0

def main():
 d=json.loads((P/'grammar66.json').read_text());prod={int(k):v for k,v in d['productions'].items()};words=freeze(d['words'])
 expected=[]
 for t in e.combined_word():expected.append(('leaf',t[0],t[1])if not isinstance(t,str)else t)
 assert words[d['root']]==tuple(expected)
 mins={};witness={};cost=0
 for k in sorted(prod,key=lambda k:len(words[k])):
  p=prod[k]
  if p[0]=='FREE':
   assert (len(words[k]),p[1])in[(2,99),(4,190)]
   assert all(x==('leaf','inc',1)for x in words[k])
   mins[k]=1 if p[1]==99 else 2;witness[k]=['FREE',p[1]];continue
  assembled=[]
  for typ,v in p:
   assembled.extend(words[v]if typ=='word'else[freeze(v)])
  assert tuple(assembled)==words[k]
  assert len(p)>=2
  cost+=len(p)-1
  typ,v=p[0]
  # The first part lies below at least one left edge under every association
  # of two or more ordered parts. This is a rigorous lower bound, sufficient
  # to exhibit the forbidden run; no particular random association is used.
  mins[k]=1+(mins[v]if typ=='word'else token_leading(freeze(v)))
  witness[k]=['left_first_part',typ,v]
 assert cost==66
 used=set()
 def visit(k):
  if k in used:return
  used.add(k)
  if prod[k][0]!='FREE':
   for typ,v in prod[k]:
    if typ=='word':visit(v)
 visit(d['root'])
 bad=sorted(k for k in used if mins[k]>6)
 assert 208 in bad and mins[208]>=7
 chain=[];k=208
 while True:
  chain.append({'word_id':k,'word':words[k],'minimum_leading_zeros':mins[k],'production':prod[k]})
  p=prod[k]
  if p[0]=='FREE' or p[0][0]!='word':break
  k=p[0][1]
 out={'macro_tokens':len(expected),'fixed_dictionary_binary_cost':cost,
      'used_dictionary_words':len(used),'offending_word':208,
      'lower_bound_on_consecutive_zeros':mins[208],'inherited_limit':6,
      'first_part_chain':chain,
      'scope':'This fixed dictionary forces a zero run exceeding the inherited bound. No global state or grammar lower bound.'}
 (P/'obstruction.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k!='first_part_chain'},indent=2))
if __name__=='__main__':main()
