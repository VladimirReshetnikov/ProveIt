#!/usr/bin/env python3
"""Independent direct-formula replay; reads circuit/source data, imports no builders."""
import json,gzip,hashlib,random,collections,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def req(x,s):
 if not x:raise ValueError(s)
def load(p):return json.loads((ROOT/p).read_text())
PORTS={}
for name,file in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
 raw=gzip.decompress((ROOT/'coefficients/payloads'/f'{file}.bin.gz').read_bytes());PORTS[name]=int.from_bytes(raw,'little')
def recval(ts,p):return sum(t['coefficient']*math.prod(pow(PORTS[k],e,p) for k,e in zip(PORTS,t['powers'])) for t in ts)%p
def evaluate(d,x,fix,p):
 vals=[]
 for k,n in enumerate(d['nodes']):
  t=n['kind']
  if t=='literal':v=int(n['value'])
  elif t=='variable':v=x[n['name']]
  elif t=='fixed':v=fix[n['name']]
  else:
   req(0<=n['left']<k and 0<=n['right']<k,'acyclic')
   a,b=vals[n['left']],vals[n['right']];v=a+b if t=='add' else a-b if t=='sub' else a*b if t=='mul' else None
   req(v is not None,'operation')
  vals.append(v%p)
 return vals[d['output']],{n:vals[i] for n,i in d['named_nodes'].items()}
def audit_graph(d):
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i);n=d['nodes'][i]
  if 'left'in n:walk(n['left']);walk(n['right'])
 walk(d['output']);req(len(seen)==len(d['nodes']),'dead nodes')
 count=collections.Counter(n['kind'] for n in d['nodes'] if 'left'in n)
 req(dict(count)==d['operation_counts'],'gate ledger');req(sum(count.values())==d['total_operations'],'operation total')
 req(set(d['variables'])=={n['name'] for n in d['nodes'] if n['kind']=='variable'},'variable list')
 return dict(count)
def source(b,g,B,weights,rows,p):
 W=max(weights);step=2*W+1;H=len(rows)*step;K=H+2*W
 D=0
 for j,row in enumerate(rows,1):
  for a,cv in row:D+=cv*pow(B,j*step-sum(i*w for i,w in zip(a,weights)),p)
 D%=p;ell=sum(pow(B,w,p) for w in weights)%p;N0=pow(B,W+1,p);N1=4*pow(B,K+1,p)%p;N=N0*N1%p
 targets=sum(pow(B,j*step,p) for j in range(1,len(rows)+1))%p
 mask=(N0-1-(b-1)*ell)%p;T=(mask+(B-2)*targets*N0)%p
 # Literal sum, deliberately independent of the emitted geometric evaluator.
 geom=0;term=1
 for j in range(K+1):geom=(geom+term)%p;term=term*B%p
 J=(2*(1+g)**2*D+B*geom)%p;S=(g+J*N0)%p;Rc=((S+T+1)*N+T+1)%p;R=(N-1)*Rc%p
 return dict(Dcode=D,ell=ell,N0=N0,N1=N1,N=N,mask=mask,targets=targets,Tcode=T,Jcode=J,Scode=S,R=R,Rcode=Rc,Ccap=b*pow(B,W,p)%p)
def nine_rows(d,p):
 import ast
 # Restricted exact expression interpreter for symbolic coefficient data.
 names={k:v%p for k,v in PORTS.items()}
 def expr(n):
  if isinstance(n,ast.Expression):return expr(n.body)
  if isinstance(n,ast.Constant) and type(n.value)is int:return n.value
  if isinstance(n,ast.Name):return names[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -expr(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=expr(n.left),expr(n.right)
   if isinstance(n.op,ast.Add):return (a+b)%p
   if isinstance(n.op,ast.Sub):return (a-b)%p
   if isinstance(n.op,ast.Mult):return a*b%p
   if isinstance(n.op,ast.Pow):return pow(a,b,p)
  raise ValueError('expression')
 data=load('quartic/QUADRATIC_TARGETS.json')
 return [[(t['alpha'],expr(ast.parse(t['weighted_coefficient'],mode='eval'))%p) for t in r['terms']] for r in data['rows']]
def expected_nine(d,x,src,p):
 n=lambda a:a%p
 b=(pow(2,d['base_floor_exponent'],p)+x['epsilon']-1)%p;g=x['g'];h=x['h'];s=x['s'];w=x['w'];phi=x['phi']-1;i=x['i'];j=x['j'];nn=x['n']-1
 R,N,cap=src['R'],src['N'],n(32*src['Ccap'])
 U=n(N*N*w);Y=n(N*N*s);M=n(R*Y);P=n(2*M*M*U);K=n(R+1+h*(P-1));A=n(M*(U+1));B1=n(2*R+1);W=n(b*w);C=n(B1+W+phi);J=n(4*A-5);Q=n(3*W*C-2*(W*W-1));D=n((A*A-1)*C*C+1);E=n(i*J*D*C*C);F=n((A*A-1)*E*E+1);G=n(A+F*(C*D+1-A));H=n(B1+j*C);I=n((G*G-1)*H*H+1)
 a0=n((P*P-1)*K*K+1);a1=n(D*F*I);u=n(J*F);v=n(Q*F+J*(H-C));m=n((K*K-4*(C-K*Y)**2)*cap-8*g*K*K);V0=n(P*K);V1=n(A*C*A*E*G*H)
 # Final accepted variant uses the positive linear bound, or its recorded predecessor.
 Md=n(Q+H)
 Om=n(u*m);E0=n(u*(nn+Md)+v-2*Om*Md);Th=n(E0-Om*V0*V1);inner=n(Th*Th-Om*Om*(a0+V0*V0*a1));out=n(inner*inner-4*pow(Om,4,p)*V0*V0*a0*a1)
 return out,locals()
def expected_sun(x,src,p):
 n=lambda a:a%p
 f,g,h,k,l,w,xx,y,z,m=[x[v] for v in ['f','g','h','k','l','w','x','y','z','m']]
 b=n(1+3*f);X,Y,cap=src['R'],n(src['N']**2),src['Ccap'];L=n(l*Y);U=n(2*L*X);V=n(4*g*w*Y);W=n(b*w);A=n(U*(V+1));B=n(2*X+1);C=n(B+(A-2)*h);Pn=n(U*U*V);K=n(X+1+k*(Pn-2));S=n(2*A-5);T=n(3*W*C-2*(W*W-1));R2=n((Pn*Pn-4)*K*K+4);Delta=n(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K));O=n(f*f*l*l*Delta);xi=n(z*xx);D=n((A*A-4)*C*C+4);E=n(C*C*D*xi);F=n(4*(A*A-4)*E*E+1);Gs=n(2*(A+2)*(A-2)**2*E*E-1);Omega=n(16*E);Hs=n(C+(B-C)*F+Omega*F*y);Is=n((Gs*Gs-1)*Hs*Hs+1);Sigma=n(xi*pow(S,5,p));r=n(T+S*y);Theta=n((r**3-r*S*S-S**3)*(r*r+23*S*S));r0=n(b*(1+(3*O-4)*b*b*z*z));r1=R2;r2=n(D*F*Is);w1=r0;w2=n(r0*(Pn*Pn+K*K+3));center=n(Sigma*m-Theta);AA=[n(Sigma*Sigma*t*t*rv) for t,rv in [(1,r0),(w1,r1),(w2,r2)]];Vn=n(center*center+AA[2]-AA[0]-AA[1]);Wn=n(Vn*Vn+4*center*center*AA[2]-4*AA[0]*AA[1]);return n(Wn*Wn-16*Vn*Vn*center*center*AA[2])
