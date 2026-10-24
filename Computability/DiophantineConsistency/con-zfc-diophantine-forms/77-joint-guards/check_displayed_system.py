"""Independently match compact printed systems to every literal row."""
from pathlib import Path
import json,sympy as s
p=Path(__file__).resolve().parent
for filename,retain in [('joint24_degree12.json',False),('joint25_octic.json',True)]:
 d=json.loads((p/'joint'/filename).read_text());sy={n:s.Symbol(n) for n in d['variables']+d['fixed_numerals']};globals().update(sy)
 q=beta*(3*J3+1)+1;W=4*(3*w3+1);X=q*W;Y=(2*v_scale+1)*q**3
 k=1-V+j*c+h*E;H=4*a+3;Delta=a*a+H;C=q-F-alpha
 R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*(3*J3+1)
 D=cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2
 T=eta*(zeta if retain else k-eta)
 pos=1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)
 rows=[a-E-Y,E*(X+1)-a*X,c-k*(a-E)-eta,tau**2-E*(c-eta)*(k+E*(c-eta))-1,(X+a*c+gamma*H)**2-Delta*c*c-1,j*c-V-R,(K0+W)*C-F-z*(q-1),V+c-f*o,I-(2*r+1)*c*c,I*I-Delta*(f*f-1),I*I*V*V-(I*I-1)*y*y-1]
 if retain:rows.append(zeta-k+eta)
 rows.append(D*T-(pair_root**2-D-T+1)**2-pos)
 if len(rows)!=len(d['residuals']):raise RuntimeError('row count')
 for n,(a1,b1) in enumerate(zip(rows,d['residuals']),1):
  if s.expand(a1-s.sympify(b1,locals=sy))!=0:raise RuntimeError(f'{filename} row {n}')
 print('PASS',filename,len(d['variables']),'variables',len(rows),'compact residuals')


receipt={"status":"PASS","displayed_systems":["joint24_degree12.json","joint25_octic.json"],"literal_rows":25,"scope":"Exact symbolic identity of every printed compact row with its literal JSON row."}
(p/"DISPLAYED_SYSTEM_CHECK.json").write_text(json.dumps(receipt,indent=2)+"\n")
