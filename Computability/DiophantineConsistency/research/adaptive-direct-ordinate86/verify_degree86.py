"""Exact degree certificate, in the 13 witness variables with ports fixed."""
from pathlib import Path
import runpy
p=Path(__file__).resolve().parent;s=runpy.run_path(str(p/'verify_equation86.py'));checks=s['checks'];names=s['names'];witnesses=names[:13]
# Each selected witness monomial has exactly the displayed single coefficient
# as a polynomial in beta, K0, MC and MF. Hence its coefficient survives fixing
# arbitrary integer ports with beta>0.
cert=[('A',15,{'J':9,'X':2,'Y':2,'eta':2},(9,0,0,0),-2),
      ('L',13,{'J':4,'X':2,'Y':5,'eta':1,'gamma':1},(4,0,0,0),8),
      ('N',18,{'J':8,'f':6,'X':2,'Y':2},(8,0,0,0),1),
      ('S',10,{'i':2,'Y':4,'eta':4},(0,0,0,0),1)]
for name,degree,monomial,ports,coefficient in cert:
 poly=checks[name][0].d;assert max(sum(e[:13]) for e in poly)==degree
 key=tuple(monomial.get(n,0) for n in witnesses);terms={e[13:]:c for e,c in poly.items() if e[:13]==key};assert terms=={ports:coefficient},(name,terms)
 print(name,'degree',degree,'witness monomial',monomial,'coefficient',coefficient,'port exponents',ports)
# beta = (2^47)^2011 - 1 in the printed fixed constants.
beta=(2**47)**2011-1;assert beta>0
print('PASS: factor degrees 15,13,18,10; product-minus-one degree 56; positive shift preserves degree')
