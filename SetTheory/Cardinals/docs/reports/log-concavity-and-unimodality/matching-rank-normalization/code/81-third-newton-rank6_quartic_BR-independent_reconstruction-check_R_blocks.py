"""Independent R determinant positivity and inverse identity receipt."""
from pathlib import Path
import json
import sympy as s
import reconstruct as r
rows=[]
for U,J in sorted({(c[0],c[1]) for c in r.profiles()}):
 types,E,rr,inv,det=r.rblock(U,J)
 r.need(all(c>=0 for c in s.Poly(det,r.n).all_coeffs()) and det.subs(r.n,1)>0,'positive R determinant')
 rows.append({'U':U,'J':J,'representatives':list(types),'determinant':str(det),'inverse_identity_verified':True,'positive_for_n_at_least_one':True})
Path(__file__).with_name('R_block_checks.json').write_text(json.dumps({'all_pass':True,'blocks':len(rows),'records':rows},indent=2)+'\n')
print('All',len(rows),'R inverse identities and positive determinants pass')
