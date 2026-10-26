"""Multiplicative coefficient sharing through triangular monic scales.

Initialize the inherited exact shared-scale vertex-cover normalization, then
select factor pairs a*b=c to reduce a deterministic constructor cost. Exact
source pullback checking, not optimization quality, proves correctness.
"""
import math
from collections import Counter

def normalize(source):
 n=len(source['variables']);variables=[{'kind':'original','source_index':i} for i in range(n)];occ=[];needed_base={abs(c) for row in source['residuals'] for c,m in row['terms'] if abs(c)>1 and len(m)<2}
 groups=sorted({(abs(c),tuple(m)) for row in source['residuals'] for c,m in row['terms'] if abs(c)>1 and len(m)==2})
 options={}
 for c,(x,y) in groups:
  choices=[]
  for a in range(1,math.isqrt(c)+1):
   if c%a:continue
   for aa,bb in [(a,c//a),(c//a,a)]:
    fs=tuple(sorted(set((d,v) for d,v in [(aa,x),(bb,y)] if d>1)));choices.append((fs,aa,bb))
  options[c,(x,y)]=sorted(set(choices))
 from normalize import normalize as old_normalize
 old=old_normalize(source);oldsc={(v['coefficient'],v['variable']) for v in old['variables'] if v['kind']=='scale'}
 selected={};uses=Counter()
 for k in groups:
  c,(x,y)=k;aa,bb=(c,1) if (c,x) in oldsc else (1,c)
  best=next(q for q in options[k] if q[1:]==(aa,bb));selected[k]=best
  for s in best[0]:uses[s]+=1
 def count(used):
  cs=needed_base|{c for c,v in used};return len(used)+len(cs)
 for sweep in range(10):
  changed=False
  for k in groups:
   old=selected[k]
   for s in old[0]:uses[s]-=1
   active={s for s,z in uses.items() if z};best=min(options[k],key=lambda q:(count(active|set(q[0])),q))
   if count(active|set(best[0]))<count(active|set(old[0])):selected[k]=best;changed=True
   for s in selected[k][0]:uses[s]+=1
  if not changed:break
 scales_needed={s for s,z in uses.items() if z};needed=needed_base|{c for c,v in scales_needed}
 def close(c):
  choices=[a for a in {1}|needed if a<c and c-a in ({1}|needed) and c-a<c]
  if not choices and c//2>1:needed.add(c//2);close(c//2)
 for c in sorted(needed.copy()):close(c)
 constants={};rows=[]
 for c in sorted(needed):
  idx=len(variables);constants[c]=idx;variables.append({'kind':'constant','value':c});available={1}|set(constants)-{c};choices=[(a,c-a) for a in available if a<=c-a and c-a in available];parts=list(min(choices,key=lambda p:(p[1],p[0]))) if choices else [c//2,c//2]+([1] if c%2 else [])
  rows.append({'kind':'constant','value':c,'terms':[[1,[idx]]]+[[-1,[] if a==1 else [constants[a]]] for a in parts]})
 scales={}
 for c,v in sorted(scales_needed):
  idx=len(variables);scales[c,v]=idx;variables.append({'kind':'scale','coefficient':c,'variable':v});rows.append({'kind':'scale','coefficient':c,'variable':v,'terms':[[1,[idx]],[-1,[constants[c],v]]]})
 for r,row in enumerate(source['residuals']):
  terms=[]
  for c,m in row['terms']:
   a=abs(c)
   if a==1:out=list(m)
   elif not m:out=[constants[a]]
   elif len(m)==1:out=[constants[a],m[0]]
   else:
    _,aa,bb=selected[a,tuple(m)];out=[m[0] if aa==1 else scales[aa,m[0]],m[1] if bb==1 else scales[bb,m[1]]]
   terms.append([1 if c>0 else -1,out])
  rows.append({'kind':'source','source_row':r,'terms':terms})
 return {'variables':variables,'rows':rows,'original_variables':n,'constant_count':len(constants),'scale_count':len(scales)}

