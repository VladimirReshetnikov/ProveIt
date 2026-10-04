#!/usr/bin/env python3
"""Independent inert-data audit. Does not import or execute any submitted code."""
import argparse, collections, hashlib, json, pathlib, sys
ROOT=pathlib.Path('/workspace/shared/sandpile-unrestricted-stabilization-20261004')
OUT=pathlib.Path(__file__).resolve().parent
EXPECTED_HASH='8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759'
class Poly:
 def __init__(self, v=0):
  if isinstance(v,Poly): self.d=v.d
  elif isinstance(v,str): self.d={(v,):1}
  elif isinstance(v,int): self.d={():v} if v else {}
  else: self.d={m:c for m,c in v.items() if c}
 def __add__(self,b):
  b=Poly(b); d=self.d.copy()
  for m,c in b.d.items(): d[m]=d.get(m,0)+c
  return Poly(d)
 __radd__=__add__
 def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
 def __sub__(self,b): return self+-Poly(b)
 def __rsub__(self,b): return Poly(b)+-self
 def __mul__(self,b):
  b=Poly(b);d={}
  for m,c in self.d.items():
   for n,e in b.d.items():
    k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
  return Poly(d)
 __rmul__=__mul__
 def __eq__(self,b): return self.d==Poly(b).d
 def degree(self):return max(map(len,self.d),default=-1)
 def homogeneous(self,d):return {m:c for m,c in self.d.items() if len(m)==d}
def need(condition,message):
 if not condition: raise ValueError(message)
W=set();EQ={};MAC={}
def pos(n):
 need(n not in W,'duplicate expected variable '+n);W.add(n);return Poly(n)
def natural(n):return pos(n+'.Plus')-1
def equation(n,l,r):
 need(n not in EQ,'duplicate expected equality '+n);EQ[n]=Poly(l)-r
def macro(kind,name,**kw):
 need(name not in MAC,'duplicate expected macro '+name);MAC[name]={'kind':kind,**{k:Poly(v) for k,v in kw.items()}}
def powrel(b,n,k):
 b,n=Poly(b),Poly(n);o=pos(k+'.out');a=pos(k+'.aMinus1')+1;beta=pos(k+'.betaMinus1')+1
 w,M,g,x,y,u,v,s,t,qb,qv,st=[pos(k+'.'+z) for z in ['w','M','g','x','y','u','v','s','t','qb','qv','strict']]
 dwb,dwk,dyk,al1,al2,sg1,sg2,ta1,ta2,rh1,rh2=[natural(k+'.'+z) for z in ['dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2']]
 index=n+1; m=b*o
 # Clauses are specified algebraically, independently of emitted operation order.
 residuals=[x*x-1-(a*a-1)*y*y,u*u-1-(a*a-1)*v*v,s*s-1-(beta*beta-1)*t*t,
 beta-1-4*y*qb,beta-a+u*(al1-al2),v-y*y*qv,s-x+u*(sg1-sg2),
 t-index+4*y*(ta1-ta2),y-index-dyk,w-b-dwb,w-index-dwk,M-m-st,
 a*a-1-((w+1)*(w+1)-1)*w*w*g*g,2*a*b-M-b*b-1,
 x-y*(a-b)-m+M*(rh1-rh2)]
 for i,e in enumerate(residuals,1):equation(k+'.eq'+str(i),e,0)
 macro('power',k,base=b,exponent=n,out=o);return o
def geom(b,n,k):
 end=powrel(b,n,k+'.power');v=natural(k+'.value');equation(k+'.geometric',(b-1)*v+1,end)
 macro('geometric',k,base=b,length=n,out=v);return v
def subset(M,U,k):
 ell=powrel(2,M+1,k+'.radix');P=powrel(ell,U,k+'.position');E=powrel(ell+1,M,k+'.expansion')
 q,h,r=[natural(k+'.'+v) for v in ['quotient','half','remainder']];ds=pos(k+'.digitSlack');rs=pos(k+'.remainderSlack')
 equation(k+'.extract',E-(q*ell+2*h+1)*P,r);equation(k+'.digitBound',2*h+1+ds,ell);equation(k+'.remainderBound',r+rs,P)
 macro('subset',k,mask=M,value=U)
def intersect(X,Y,k):
 W0,A,C=[natural(k+'.'+v) for v in ['common','leftOnly','rightOnly']]
 equation(k+'.partitionLeft',X-W0,A);equation(k+'.partitionRight',Y-W0,C)
 subset(X,W0,k+'.left');subset(Y,W0,k+'.right');subset(A+C,A,k+'.disjoint')
 macro('and',k,left=X,right=Y,out=W0);return W0
def spread(V,b,n,s,k):
 gap=natural(k+'.strideGap');slack=pos(k+'.rangeSlack')
 equation(k+'.strideBound',s-n-1,gap)
 P=powrel(b,n,k+'.range');equation(k+'.rangeBound',P-V,slack)
 C=powrel(b,s-1,k+'.copyBase');E=powrel(C,n,k+'.copyEnd');G=natural(k+'.copying');J=natural(k+'.masking')
 equation(k+'.copyGeom',(C-1)*G+1,E);equation(k+'.maskGeom',(b*C-1)*J+1,E*P)
 O=intersect(V*G,(b-1)*J,k+'.select');macro('spread',k,value=V,base=b,length=n,stride=s,out=O);return O
def stable(J,k,raw=None):
 bits=[natural(k+'.bit'+str(i)) for i in range(3)]
 for i,B in enumerate(bits):subset(J,B,k+'.allow'+str(i))
 subset(J,bits[1]+bits[2],k+'.exclude67');O=bits[0]+2*bits[1]+4*bits[2]
 if raw is not None:equation(k+'.reconstruct',raw,O)
 macro('stable',k,mask=J,out=O);return O
p,q,r,d,e,f=[pos('descriptor.'+v) for v in ['p','q','r','d','e','f']]
T=natural('descriptor.tile');D=natural('descriptor.patch');fields=[p-1,q-1,r-1,T,d-1,e-1,f-1,D]
suffix=D
for j in reversed(range(7)):
 c=Poly('InputPlus')-1 if j==0 else natural('descriptor.pair'+str(j));a=fields[j]
 equation('descriptor.cantor'+str(j),2*c,(a+suffix)*(a+suffix+1)+2*suffix);suffix=c
nt=p*q*r;nd=d*e*f
Jt=geom(Poly(32),nt,'tile.externalMask');stable(Jt,'tile.externalDigits',T)
Jd=geom(Poly(32),nd,'patch.externalMask');subset(15*Jd,D,'patch.externalDigits')
L=pos('radix.precision');b=powrel(32,L,'radix.base');h=pos('radix.sixteenth');equation('radix.sixteenthEquation',16*h,b)
Tb=spread(T,Poly(32),nt,L,'tile.convert');Db=spread(D,Poly(32),nd,L,'patch.convert')
tx,ty,tz=[pos('box.t'+axis)+1 for axis in ['x','y','z']]
hx=p*d*tx;hy=q*e*ty;hz=r*f*tz;A=2*hx;B=2*hy;C=2*hz;AB=A*B
br=powrel(b,p,'tile.rowBase');tr=spread(Tb,br,q*r,2*d*tx,'tile.rows')
bp=powrel(b,A*q,'tile.planeBase');te=spread(tr,bp,r,2*e*ty,'tile.planes')
rx=geom(br,2*d*tx,'tile.repeatX');ry=geom(bp,2*e*ty,'tile.repeatY');bz=powrel(b,AB*r,'tile.zBase');rz=geom(bz,2*f*tz,'tile.repeatZ');H=te*rx*ry*rz
pr=powrel(b,d,'patch.rowBase');dr=spread(Db,pr,e*f,2*p*tx,'patch.rows');pp=powrel(b,A*e,'patch.planeBase');de=spread(dr,pp,f,2*q*ty,'patch.planes');ps=powrel(b,hx+A*hy+AB*hz,'patch.shift');Delta=de*ps
X=powrel(b,A,'box.X');Y=powrel(X,B,'box.Y');Q=powrel(Y,C,'box.Q')
J=natural('box.J');jx,jy,jz=[natural('box.j'+axis) for axis in ['x','y','z']]
equation('box.JEquation',(b-1)*J+1,Q);equation('box.jxEquation',b*b*((b-1)*jx+1),X);equation('box.jyEquation',X*X*((X-1)*jy+1),Y);equation('box.jzEquation',Y*Y*((Y-1)*jz+1),Q)
I=b*X*Y*jx*jy*jz;cap=h-1;U=natural('supersolution.U');subset(cap*I,U,'supersolution.support')
nx,ny,nz=[natural('supersolution.negative'+axis) for axis in ['x','y','z']]
for k,base,z in [('X',b,nx),('Y',X,ny),('Z',Y,nz)]:equation('supersolution.div'+k,base*z,U)
F=stable(J,'endpoint');left=H+Delta+b*U+X*U+Y*U+nx+ny+nz;right=6*U+F;equation('sandpile.balance',left,right)
PORT=dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=T,patch=D,tile_size=nt,patch_size=nd,precision=L,radix=b,sixteenth=h,capacity=cap,tile_converted=Tb,patch_converted=Db,half_x=hx,half_y=hy,half_z=hz,A=A,B=B,C=C,X=X,Y=Y,Q=Q,background=H,additions=Delta,all_slots=J,interior_mask=I,supersolution=U,endpoint=F,balance_left=left,balance_right=right)
# Read the submitted data only after deriving the independently specified system.
parser=argparse.ArgumentParser();parser.add_argument('--dag',type=pathlib.Path,default=ROOT/'evidence/polynomial-dag.json');parser.add_argument('--allow-unsealed-test-data',action='store_true');parser.add_argument('--receipt',type=pathlib.Path,default=OUT/'exact-receipt.json');args=parser.parse_args()
raw=args.dag.read_bytes();dag=json.loads(raw)
if args.allow_unsealed_test_data:need(args.dag.resolve()!=(ROOT/'evidence/polynomial-dag.json').resolve(),'cannot unseal original')
else:need(hashlib.sha256(raw).hexdigest()==EXPECTED_HASH,'wrong frozen DAG')
need(dag['schema']=='fixed-positive-integer-polynomial-dag-v1','schema');need(dag['input']=='InputPlus','input')
need(len(dag['witnesses'])==len(set(dag['witnesses'])),'duplicate DAG variable');need(set(dag['witnesses'])==W,'variable mismatch')
need(dag['domain']=='InputPlus and every witness are strictly positive integers','domain')
values={'input:InputPlus':Poly('InputPlus'),**{'witness:'+w:Poly(w) for w in W}}
def value(ref):
 if ref.startswith('constant:'):
  z=ref.split(':',1)[1];v=int(z);need(str(v)==z,'noncanonical constant');return Poly(v)
 need(ref in values,'forward or invalid reference '+ref);return values[ref]
body=dag['body_gate_count'];need(type(body)==int and 0<body<len(dag['gates']),'body index')
for i,gate in enumerate(dag['gates']):
 need(type(gate)==list and len(gate)==3,'arity');op,a,z=gate;need(op in ['+','-','*'],'primitive')
 if i<body:
  aa,zz=value(a),value(z);values['gate:'+str(i)]={'+':lambda:aa+zz,'-':lambda:aa-zz,'*':lambda:aa*zz}[op]()
 else:
  for ref in [a,z]:
   if ref.startswith('gate:'):need(0<=int(ref[5:])<i,'tail forward reference')
   elif not ref.startswith('constant:'):need(ref in values,'tail undeclared leaf')
seen=set();degrees={};tops={}
for l,r,n in dag['equalities']:
 need(n not in seen,'duplicate DAG equality');seen.add(n);need(n in EQ,'unexpected equality '+n)
 actual=value(l)-value(r);expect=EQ[n]
 # Expected equations sometimes deliberately reverse both sides.
 need(actual==expect or actual==-expect,'polynomial mismatch '+n)
 deg=actual.degree();degrees[n]=deg
 if deg==9:tops[n]=[{'variables':list(m),'coefficient':c} for m,c in sorted(actual.homogeneous(9).items())]
need(seen==set(EQ),'missing equality')
seenm=set()
for m in dag['macros']:
 name=m['name'];need(name not in seenm,'duplicate macro');seenm.add(name);need(name in MAC,'unexpected macro')
 target=MAC[name];need(m['kind']==target['kind'],'macro kind');need(set(m)-{'name'}==set(target),'macro port set')
 for k,v in target.items():
  if k!='kind':need(value(m[k])==v,'macro port mismatch '+name+':'+k)
need(seenm==set(MAC),'missing macro');need(set(dag['ports'])==set(PORT),'public ports')
for k,v in PORT.items():need(value(dag['ports'][k])==v,'port mismatch '+k)
# Verify the exact sum of squares structurally, not by trusting its description.
N=len(EQ);need(len(dag['gates'])==body+3*N-1,'SOS length');squares=[]
for j,(l,r,n) in enumerate(dag['equalities']):
 i=body+2*j;need(dag['gates'][i]==['-',l,r],'SOS residual');ref='gate:'+str(i);need(dag['gates'][i+1]==['*',ref,ref],'SOS square');squares.append('gate:'+str(i+1))
acc=squares[0]
for j,ref in enumerate(squares[1:]):
 i=body+2*N+j;need(dag['gates'][i]==['+',acc,ref],'SOS sum');acc='gate:'+str(i)
need(acc==dag['output'],'wrong output')
live=set();todo=[dag['output']]
while todo:
 ref=todo.pop()
 if ref in live:continue
 live.add(ref)
 if ref.startswith('gate:'):todo.extend(dag['gates'][int(ref[5:])][1:])
need(all('gate:'+str(i) in live for i in range(len(dag['gates']))),'dead gate');need(all('witness:'+w in live for w in W),'dead witness');need('input:InputPlus' in live,'dead input')
maxdeg=max(degrees.values());top=Poly()
for n,e in EQ.items():
 if e.degree()==maxdeg:
  v=Poly(e.homogeneous(maxdeg));top+=v*v
need(maxdeg==9 and top.degree()==18,'exact degree')
count=lambda xs:dict(collections.Counter(x[0] for x in xs))
receipt={'status':'PASS','dag_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':len(W),'residuals':N,'gates':len(dag['gates']),'body_gates':body,'body_counts':count(dag['gates'][:body]),'sos_counts':count(dag['gates'][body:]),'total_counts':count(dag['gates']),'macro_counts':dict(collections.Counter(m['kind'] for m in dag['macros'])),'macro_records_exactly_checked':len(MAC),'ports_exactly_checked':len(PORT),'max_residual_degree':maxdeg,'exact_final_degree':2*maxdeg,'degree_nine_residuals':tops,'degree_eighteen_homogeneous_part':[{'variables':list(m),'coefficient':c} for m,c in sorted(top.d.items())],'dead_gates':0,'dead_witnesses':0,'largest_normalized_body_gate_terms':max(len(v.d) for v in values.values()),'submitted_programs_executed':False}
args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,indent=2,sort_keys=True))
