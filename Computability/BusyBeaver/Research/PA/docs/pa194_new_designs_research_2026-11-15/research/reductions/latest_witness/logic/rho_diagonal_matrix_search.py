#!/usr/bin/env python3
"""Finite algebra screen for the proposed u=D restriction of rho8.

Value 0 is designated. Modus ponens and the zero alias I(0,0)=0 are
imposed. This is a finite screen, not a completeness decision procedure.
"""
import itertools,json
from pathlib import Path
n=3;checked=0;models=0;counter=[]
for first in itertools.product(range(1,n),repeat=n-1):
 for rest in itertools.product(range(n),repeat=n*(n-1)):
  tab=(0,)+first+rest;checked+=1
  def I(a,b):return tab[n*a+b]
  if not all(I(I(I(h,d),d),I(I(d,h),I(a,h)))==0 for a,d,h in itertools.product(range(n),repeat=3)):continue
  models+=1;failed={}
  for a,b,c in itertools.product(range(n),repeat=3):
   vals={'K':I(a,I(b,a)),'S':I(I(a,I(b,c)),I(I(a,b),I(a,c))),'Peirce':I(I(I(a,b),a),a)}
   for k,v in vals.items():
    if v!=0 and k not in failed:failed[k]={'a':a,'b':b,'c':c,'value':v}
  if failed:counter.append({'table':[tab[i*n:(i+1)*n] for i in range(n)],'failed':failed})
out={'scope':'three-valued, designated zero, MP-preserving, zero alias','tables_checked':checked,'axiom_models':models,'countermodels':counter}
Path(__file__).with_name('rho_diagonal_matrix_search.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
