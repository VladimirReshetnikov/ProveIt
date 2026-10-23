if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Independent actual-tuple, fixed-index, circuit and root-bound diagnostics.
All inputs are inert JSON or byte arrays; no received program is executed.
"""
import argparse,json,sys,hashlib,itertools,random,math
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'review'))
from optimize_nine_circuit import evaluate,audit_body

def homogeneous4(B,nu,p):
 r=5**nu;hs=[1,0,0,0,0]
 for ex in [r]+[r-5**i for i in range(nu+1)]:
  t=pow(B,ex,p)
  for j in range(1,5):hs[j]=(hs[j]+t*hs[j-1])%p
 return pow(B,r,p)*hs[4]%p

def alpha_terms(nu):
 # Four unordered stars, one slack category, one category for each real coordinate.
 weights=[0]+[5**i for i in range(nu+1)]
 for places in itertools.combinations_with_replacement(range(nu+2),4):
  yield sum(weights[j] for j in places)
def fixed_data(c,ports,p):
 fixed={'z_index':pow(2,c['index_exponent'],p)};z=fixed['z_index'];B=2*z%p;L=c['L']
 for r in c['coefficient_records']:
  v=0
  for term in r['coefficient_polynomial_in_fixed_ports']:
   x=term['coefficient']
   for n,e in zip(ports,term['powers']):x=x*pow(n%p,e,p)%p
   v=(v+x)%p
  fixed[r['name']]=v
 sparse=sum(fixed[r['name']]*pow(B,L-r['expo'],p) for r in c['coefficient_records'])%p
 y=(z*homogeneous4(B,c['nu'],p)+sparse)%p
 literal_baseline=sum(pow(B,L-e,p) for e in alpha_terms(c['nu']))%p
 assert homogeneous4(B,c['nu'],p)==literal_baseline
 fixed['y_index']=y
 return fixed

def direct(c,f,v,p):
 z=f['z_index'];y=f['y_index'];L=c['L'];nu=c['nu']
 eps,g0,h0,s0,w0,phi,i0,j0,n=[v[x] for x in ('epsilon','g0','h0','s0','w0','phi','i0','j0','n')]
 g,h,s,w,i,j=[x+1 for x in (g0,h0,s0,w0,i0,j0)]
 b=(y+1+eps)%p;B=pow(b,5,p);q=pow(B,L,p);N=pow(q,16,p)
 ell=sum(pow(B,5**r,p) for r in range(1,nu+1))%p
 lam=((pow(B,4*L,p)-1)*pow(B-1,-1,p))%p if B!=1 else 4*L%p
 e=(z*homogeneous4(B,nu,p)+sum(f[r['name']]*pow(B,L-r['expo'],p) for r in c['coefficient_records']))%p
 R=((g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)+(q**3-b*ell+ell+(B-2*z)*lam*q**3+(B-2)*q**8)*(N*N-1))%p
 U=N*N*w%p;Y=N*N*s%p;M=R*Y%p;P=2*M*M*U%p;K=(R+1+h*(P-1))%p;A=M*(U+1)%p;Bp=(2*R+1)%p;Ws=b*w%p;C=(Bp+Ws+phi)%p;J=(4*A-5)%p;Q=(3*Ws*C-2*(Ws*Ws-1))%p;D=((A*A-1)*C*C+1)%p;E=i*J*D*C*C%p;F=((A*A-1)*E*E+1)%p;Gp=(A+F*(C*D+1-A))%p;H=(Bp+j*C)%p;I=((Gp*Gp-1)*H*H+1)%p
 a0=((P*P-1)*K*K+1)%p;a1=D*F*I%p;div=(J*F)**2%p;dvnd=(Q*F+J*(H-C))**2%p;Gcap=32*b*pow(B,5**nu,p)%p;margin=(K*K*Gcap-4*(C-K*Y)**2*Gcap-8*g*K*K)%p
 deltaR=32*z*lam*g**4*pow(q,7,p)*(N*N-N)%p;Rb=(R+deltaR)%p;Kb=(Rb+1+h*(P+1))%p;Ab=Rb*Y*(U+1)%p;Cb=(2*Rb+1+b*w+phi)%p;Jb=(4*Ab+5)%p;Db=((Ab*Ab+1)*Cb*Cb+1)%p;Eb=i*Jb*Db*Cb*Cb%p;Fb=((Ab*Ab+1)*Eb*Eb+1)%p;Gb=(Ab+Fb*(Cb*Db+1+Ab))%p;Hb=(2*Rb+1+j*Cb)%p;V0=((P+1)*Kb+2)%p;V1=(((Ab+1)*Cb+1)*((Ab+1)*Eb+1)*((Gb+1)*Hb+1)+1)%p
 W=div*(2*margin-1)%p;T=(div*n+dvnd-W*(dvnd+V0*V1))%p;inner=(T*T-W*W*(a0+V0*V0*a1))%p;out=(inner*inner-4*W**4*V0*V0*a0*a1)%p
 return dict(zip(('b','B','q','N','ell','lambda','e','R','U','Y','M','P','K','A','Wsmall','C','J','Q','D','E','F','Gp','H','I','a0','a1','divisor','dividend','Gcap','margin','deltaR','Rbar','Kbar','Abar','Cbar','Jbar','Dbar','Ebar','Fbar','Gbar','Hbar','V0','V1','W','T','inner','output'),(b,B,q,N,ell,lam,e,R,U,Y,M,P,K,A,Ws,C,J,Q,D,E,F,Gp,H,I,a0,a1,div,dvnd,Gcap,margin,deltaR,Rb,Kb,Ab,Cb,Jb,Db,Eb,Fb,Gb,Hb,V0,V1,W,T,inner,out)))

def root_diagnostics():
 rng=random.Random(32957);count=0
 for _ in range(512):
  R=rng.randrange(-10,11);Rb=abs(R)+rng.randrange(5);U,Y,b,h,i,j,w=[rng.randrange(1,5) for _ in range(7)];phi=rng.randrange(5)
  M=R*Y;P=2*M*M*U;K=R+1+h*(P-1);A=M*(U+1);C=2*R+1+b*w+phi;J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1;G=A+F*(C*D+1-A);H=2*R+1+j*C;I=(G*G-1)*H*H+1
  Kb=Rb+1+h*(P+1);Ab=Rb*Y*(U+1);Cb=2*Rb+1+b*w+phi;Jb=4*Ab+5;Db=(Ab*Ab+1)*Cb*Cb+1;Eb=i*Jb*Db*Cb*Cb;Fb=(Ab*Ab+1)*Eb*Eb+1;Gb=Ab+Fb*(Cb*Db+1+Ab);Hb=2*Rb+1+j*Cb
  for orig,bar in ((K,Kb),(A,Ab),(C,Cb),(J,Jb),(D,Db),(E,Eb),(F,Fb),(G,Gb),(H,Hb)):assert abs(orig)<=bar
  V0=(P+1)*Kb+2;V1=((Ab+1)*Cb+1)*((Ab+1)*Eb+1)*((Gb+1)*Hb+1)+1
  assert abs((P*P-1)*K*K+1)<=(V0-1)**2;assert abs(D*F*I)<=(V1-1)**2;assert J*F!=0;count+=1
 witnesses=0
 for r0,r1,d,k,m in itertools.product(range(4),range(4),range(1,5),range(3),range(1,4)):
  V0=r0+2;V1=r1+2;c=d*k;Z=c+V0*V1+r0+V0*r1;n=(2*m-1)*Z-k;W=d*(2*m-1);T=d*n+c-W*(c+V0*V1)
  assert n>=0;assert (T*T-W*W*(r0*r0+V0*V0*r1*r1))**2-4*W**4*V0*V0*r0*r0*r1*r1==0;witnesses+=1
 return dict(companion_assignments=count,constructed_finalizer_witnesses=witnesses)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('directory',type=Path,nargs='?',default=HERE/'nu31');parser.add_argument('--compiler-root',type=Path,default=HERE.parent/'compiler');args=parser.parse_args();directory=args.directory;c=json.loads((directory/'COMPACT_CONSTANTS.json').read_text());body=json.loads((directory/'nine_compact_magnitude_tight.json').read_text())
 mp=args.compiler_root;manifest=json.loads((mp/'COMPACT_COEFFICIENT_BINDING.json').read_text());files={r['name']:r for r in manifest['files']};ports=[];receipt={}
 for k in ('beta','K','MC','MF_source'):
  r=files[k];blob=(mp/r['path']).read_bytes();assert hashlib.sha256(blob).hexdigest()==r['sha256'];n=int.from_bytes(blob,'little');assert n.bit_length()==r['bit_length'];ports.append(n);receipt[k]=dict(bit_length=n.bit_length(),sha256=r['sha256'])
 assert ports[0]+1==1<<9765625
 count=0;outputs=[]
 for p in (101,1009,65537,1000000007):
  fixed=fixed_data(c,ports,p)
  for vals in ([0]*9,[1]*9,list(range(9)),[8,3,0,5,1,0,4,2,9]):
   v=dict(zip(('epsilon','g0','h0','s0','w0','phi','i0','j0','n'),vals));out=evaluate(body,fixed,v,p);a=direct(c,fixed,v,p)
   for name,node in body['named_nodes'].items():assert out[node]==a[name]%p,(p,vals,name,out[node],a[name]);count+=1
   outputs.append(dict(prime=p,inputs=vals,output=out[body['output']]))
 result=dict(status='PASS',nu=c['nu'],compiler_ports=receipt,index_exponent=c['index_exponent'],literal_index_baseline_terms=c['bounded_sum_cardinality'],actual_instance_named_node_comparisons=count,circuit=audit_body(body),diagnostics=root_diagnostics(),outputs=outputs)
 (directory/'ACTUAL_INSTANCE_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('outputs','compiler_ports')},indent=2))
if __name__=='__main__':main()
