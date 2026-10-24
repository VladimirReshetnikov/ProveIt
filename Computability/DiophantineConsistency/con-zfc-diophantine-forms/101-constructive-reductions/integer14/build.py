import sys,json
from pathlib import Path
BASE=Path(__file__).resolve().parent/'upstream'
sys.path.insert(0,str(BASE))
from build_equations import DAG,Expr,export,BASE_PORTS,VARS13

def cleared_norm4(center,A,B,Dm,Cn,delta):
 q0=delta*(center*center+Dm-A-B)-Cn;q1=-2*delta*center;Tn=delta*delta*A*B;Rn=delta*Cn
 t0=q0*q0+Dm*q1*q1-4*(Tn+Rn*(A+B));t1=2*q0*q1;z64=64*Tn*Rn
 f0=t0*t0+Dm*t1*t1-z64*(center*center+Dm);f1=2*t0*t1+2*z64*center
 return f0*f0-Dm*f1*f1

def make(shift=1, lam=4):
 vs=VARS13+['p1'];d=DAG(vs);x={n:d.leaf('variable',n) for n in vs};p={n:d.leaf('coefficient',n) for n in BASE_PORTS}
 J=6*x['j']+1;q=p['beta']*J+1;W=12*x['w']+4;X=q*W;Y=q*x['v'];E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H
 C=x['C'];F=(p['K0']+W)*C-x['z']*(q-1);R=(q*(q-F)-C)*(q*q-1)+(p['MC']+q*p['MF'])*J
 k=R+1+x['h']*E;c=x['c'];eta=c-Y*k;zeta=k-eta;c2=c*c;I=(2*x['r']+1)*c2;I2=I*I;Df=1+Delta*I2;Q=Delta*(Df-1);delta=Q-1
 V=Df*(c*x['T']-R)-c;Cy=Q*V*V-1;ell0=E*Y;L=ell0*k;Dtau=ell0*(ell0+1)*(k*k)+1;Dmain=1+Delta*c2;b0=X+a*c
 coneU=p['cone_A']*F;coneZ=p['cone_B']*C;G=coneU*coneZ-(q-coneU-coneZ)**2;Peta=eta*zeta;Gv=x['v']**2*G
 Pair=Gv*Peta-(x['t']**2-Gv-Peta+1)**2
 guard=Pair-1-x['p1']**2-x['p2']**2-x['p3']*(x['p3']+1);S=guard*guard
 F0=(a+2)*I
 if shift==1:
  M=2*q*q;U=M*H;ML=lam*U+M;U2=U*U
  center=U*(x['n']+V)+ML*b0+H*(x['v']-q*q)
  A=U2*Df;B=U2*Dtau;Dm=ML*ML*Dmain;Cn=U2*Cy
 else:
  M=4*q*q;U=M*H;ML=lam*U+M;U2=U*U
  tail=2*V
  if shift>=2:tail=tail+2*L+k
  if shift>=3:tail=tail+2*F0
  center=U*(x['n']+tail)+2*ML*b0+2*H*(x['v']-q*q)
  A=4*U2*Df;B=4*U2*Dtau;Dm=4*ML*ML*Dmain;Cn=4*U2*Cy
 N=cleared_norm4(center,A,B,Dm,Cn,delta);output=N+S+N*S
 rr={n:v for n,v in locals().copy().items() if isinstance(v,Expr)}
 packet=export('crt14_degree'+str(540 if shift==3 else 568),d,output,rr,dict(exact_degree=540 if shift==3 else 568, norm_exact_degree=484 if shift==3 else 512, proof='PROOF.md', coefficient_binding_detail='The six complete fixed integers of upstream/coefficients/BINDING.json'))
 packet['coefficient_binding']='upstream/coefficients/BINDING.json'
 return packet

def build(centered=True):
 return make(3 if centered else 1,0)

if __name__=='__main__':
 here=Path(__file__).resolve().parent
 for centered in (True,False):
  packet=build(centered)
  (here/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
  print(packet['name'],packet['variable_count'],packet['exact_degree'],packet['operations'])
