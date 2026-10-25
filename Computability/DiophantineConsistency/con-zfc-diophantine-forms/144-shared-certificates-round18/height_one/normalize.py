"""Sparse coefficient normalization with shared scale-factor vertex covers.

Every constructor is monic. Selection is heuristic; exact pullback checking
is independent of its optimization. Standard library only.
"""
from collections import defaultdict,Counter

def normalize(source):
 n=len(source['variables']);variables=[{'kind':'original','source_index':i} for i in range(n)];needed={abs(c) for r in source['residuals'] for c,m in r['terms'] if abs(c)>1}
 # Prefer a sum of two already-needed smaller constants. Only introduce a
 # binary intermediate when no such sum exists; this terminates by descent.
 def close(c):
  choices=[a for a in {1}|needed if a<c and c-a in ({1}|needed) and c-a<c]
  if not choices and c//2>1:
   needed.add(c//2);close(c//2)
 for c in sorted(needed.copy()):close(c)
 constants={};rows=[]
 for c in sorted(needed):
  idx=len(variables);constants[c]=idx;variables.append({'kind':'constant','value':c});available={1}|set(constants)-{c}
  choices=[(a,c-a) for a in available if a<=c-a and c-a in available]
  parts=list(min(choices,key=lambda p:(p[1],p[0]))) if choices else [c//2,c//2]+([1] if c%2 else [])
  terms=[[1,[idx]]]+[[-1,[] if a==1 else [constants[a]]] for a in parts]
  rows.append({'kind':'constant','value':c,'terms':terms})
 edgegroups=defaultdict(set)
 for r in source['residuals']:
  for c,m in r['terms']:
   if abs(c)>1 and len(m)==2:edgegroups[abs(c)].add(tuple(sorted(m)))
 covers={}
 for c,edges in sorted(edgegroups.items()):
  selected={a for a,b in edges if a==b};remaining={e for e in edges if not selected.intersection(e)}
  while remaining:
   degree=Counter(v for edge in remaining for v in set(edge));v=min(degree,key=lambda v:(-degree[v],v));selected.add(v);remaining={e for e in remaining if v not in e}
  covers[c]=selected
 scales={}
 for c,selected in sorted(covers.items()):
  for v in sorted(selected):
   idx=len(variables);scales[c,v]=idx;variables.append({'kind':'scale','coefficient':c,'variable':v});rows.append({'kind':'scale','coefficient':c,'variable':v,'terms':[[1,[idx]],[-1,[constants[c],v]]]})
 for r,row in enumerate(source['residuals']):
  terms=[]
  for c,m in row['terms']:
   a=abs(c)
   if a==1:out=list(m)
   elif not m:out=[constants[a]]
   elif len(m)==1:out=[constants[a],m[0]]
   else:
    v=m[0] if m[0] in covers[a] else m[1];other=m[1] if v==m[0] else m[0];out=[scales[a,v],other]
   terms.append([1 if c>0 else -1,out])
  rows.append({'kind':'source','source_row':r,'terms':terms})
 return {'variables':variables,'rows':rows,'original_variables':n,'constant_count':len(constants),'scale_count':len(scales)}
