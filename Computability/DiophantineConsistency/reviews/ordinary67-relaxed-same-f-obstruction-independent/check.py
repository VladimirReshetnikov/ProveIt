#!/usr/bin/env python3
"""Independent matrix-power and finite Pell checks, no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary67-relaxed-same-f-obstruction';L=D/'Lean/DiophantineConsistency'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for f,h in [(P/'check.py','d115178263bb7dcdd458b2d48f083ab67c39029bbf77eb6d4427d52134489657'),(P/'result.json','1eddfbdc50e47fe9c23e427a18a5445a66c5012824e5cf72750033e3212a8c1c'),(L/'ArithmeticPellIndexDivisibility.lean','47acf0a43bb3f0116f959efdbf84712bd5cd9bd2accd391f819cef0fa657c9c9'),(L/'ArithmeticPellRecurrence.lean','63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16')]:need(H(f)==h,'pin '+str(f))
src=(L/'ArithmeticPellIndexDivisibility.lean').read_text().split('theorem relaxed_auxiliary (',1)[1].split(' := by',1)[0]
for term in ('(hp : 0<p)','(hi : 0<i)','(hf : 0<f)','(hcp : c=ycoord p a)','(hbig : (a+2)*delta a*delta a<c)','p∣m ∧ c∣m','i*c*c=delta a*ycoord m a'):need(term in src,'theorem hypothesis/conclusion '+term)
# Different algorithm from author's pair multiplication: binary powering of 2x2 matrices.
def mmul(A,B,m):return tuple(tuple(sum(A[i][k]*B[k][j] for k in (0,1))%m for j in (0,1)) for i in (0,1))
def mpow(A,n,m):
 R=((1,0),(0,1))
 while n:
  if n&1:R=mmul(R,A,m)
  A=mmul(A,A,m);n//=2
 return R
def iterpell(A,n):
 d=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+d*y,x+A*y
 return x,y
results={}
for A,p,expected_c,expected_r,expected_i in [(3,4,204,10404,2),(191,6,8134013891706,11027030331744364582598406,6080)]:
 d=A*A-1;xp,c=iterpell(A,p);need(c==expected_c and c>A*d*d and c%p==0,'main ordinate and bounds');m=c;need(m%p==0 and m%c==0,'indices');M=mpow(((A,d),(1,A)),m,c*c);r=M[1][0];xmod=M[0][0];need(r==expected_r and r!=0 and (d*r)%(c*c)==0 and d*r//(c*c)==expected_i and (xmod*xmod-d*r*r)%(c*c)==1,'modular obstruction');results[str(A)]={'c':c,'main_root':xp,'m':m,'y_mod_c2':r,'i_mod_Delta':expected_i}
 if A==3:
  f,y=iterpell(A,m);i,rem=divmod(d*y,c*c);need(rem==0 and i>0 and i%d==2 and f*f-d*y*y==1 and (i*c*c)**2==d*(f*f-1) and y%(c*c)==r,'small full Pell equality')
q,w,s=3,2,1;X=w*q;Y=s*q**3;a=(X+1)*Y;need((X,Y,a)==(6,27,189) and a+2==191,'q-cube scale');c=results['191']['c'];eta,zeta=24,301259773742;need(c==(eta+zeta)*Y+eta and eta>0 and zeta>0,'positive c decomposition')
r=json.loads((P/'result.json').read_text());need(r['small_full_integer']['y_mod_c_squared']==results['3']['y_mod_c2'] and r['symbolic_qcube']['y_mod_c_squared']==results['191']['y_mod_c2'],'recorded residues');q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'result.json').read_bytes(),'author rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','matrix_power_residues':results,'qcube':[3,2,1,6,27,189],'scope':'Partial standard-integer Pell data; not a full graph zero, fixed-current-port witness, IΣ1 theorem or global reverse impossibility.'},indent=2,sort_keys=True))
