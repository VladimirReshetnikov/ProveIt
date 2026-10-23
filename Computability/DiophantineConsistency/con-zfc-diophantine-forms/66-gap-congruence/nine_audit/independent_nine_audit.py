"""Independent reader/reconstructor; never imports or executes a construction program."""
from pathlib import Path
import json, gzip, hashlib, random, math
from collections import Counter
import sympy as sp
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'nine'
def need(x,msg):
 if not x: raise RuntimeError(msg)
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def integer(p): return int.from_bytes(gzip.decompress(p.read_bytes()),'little')
ports=[integer(ROOT/'data'/f'{n}.bin.gz') for n in ['beta','K','MC','MF_source']]
for rec in read(HERE/'INHERITED_COEFFICIENT_BINDING.json')['payloads']:
 p=ROOT/'data'/rec['path'];raw=gzip.decompress(p.read_bytes())
 need(sha(p)==rec['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==rec['sha256'],'inherited coherent coefficient payload')
 need(len(raw)==rec['bytes'] and int.from_bytes(raw,'little').bit_length()==rec['bit_length'],'inherited payload length')

def coefficient(terms,mod=None):
 ans=sum(t['integer']*math.prod(pow(v,e) if mod is None else pow(v,e,mod) for v,e in zip(ports,t['port_powers'])) for t in terms)
 return ans if mod is None else ans%mod
fixed={}
for rec in read(ROOT/'fixed/BINDING.json'):
 p=ROOT/'fixed'/(rec['name']+'.bin.gz');raw=gzip.decompress(p.read_bytes()); v=int.from_bytes(raw,'little')
 need(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'fixed raw hash')
 need(v.bit_length()==rec['bits'],'fixed bit length')
 fixed[rec['name']]=rec['sign']*v
need(fixed['base_scale']==2**2134939,'base scale literal')
for name,v in fixed.items():
 if name.startswith('threshold_'):need(v==2**int(name.split('_')[1]),'threshold literal')
# Independently reconstruct the old unfactored majorant, not the author's DAG.
A,C,i=sp.symbols('A C i');J=4*A-5;D=(A*A-1)*C*C+1;k=i*J*C
F=1+k*k*D*D*(D-1);lam=C*D+1-A;G=A+F*lam
Nstar=2*G+lam;N1=2*k*k*D*(D-1)*lam+3*C;N2=2*k*k*(D-1)*lam;N3=2*k*k*(lam-C);N4=2*k*k*C
T6=k*((1024*D*D-512*D-128)*Nstar-64*N1-40*N2-28*N3-21*N4)
T=T6+i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048
poly=sp.Poly(T*T-2048**2*D*F*G*G,A,C,i)
defect=poly.as_dict(); stored={tuple(x['powers']):x['coefficient'] for x in read(ROOT/'data/defect.json')['terms']}
need(defect==stored,'full exact refined defect coefficients')
need(len(defect)==703,'defect terms')
need([max(e[t] for e in defect) for t in range(3)]==[15,18,6],'defect multidegrees')
need(defect[(15,18,6)]==9*2**18,'defect leader')
x=sp.symbols('x');t7=2048*x**7-1024*x**6-256*x**5-128*x**4-80*x**3-56*x*x-42*x-33
need(sp.expand(t7*t7-2048**2*x**13*(x-1))==109824*x**6+36608*x**5+18304*x**4+9984*x**3+5460*x*x+2772*x+1089,'seventh order certificate')
# Bind final source/layout/kernel copies to the previously audited carry files.
source_receipt=read(HERE.parent/'carry/VERIFICATION.json')
need(source_receipt['status']=='PASS','upstream carry audit status')
profiles={}; bindings=[]
for h in [2057,2068,2082]:
 folder=ROOT/'data'/f'H{h}';layout=read(folder/'layout.json');kernels=read(folder/'kernels.json')
 w=max(layout['weights']);need(w==116 and len(set(layout['weights']))==31,'weights')
 need(sha(folder/'source.json')==kernels['source_sha256']==layout['source_sha256'],'source pin')
 # Schema-normalized, exact mathematical kernel copy plus raw layout/source binding.
 check=next(x for x in source_receipt['checks'] if x['height']==h)
 cp=HERE.parent/'carry'/(check['name']+'_code.json');kp=HERE.parent/'carry'/(check['name']+'_kernels.json')
 need(sha(cp)==check['code_sha256']==sha(folder/'layout.json'),'audited layout rebind')
 need(sha(kp)==check['kernels_sha256'],'audited kernel raw hash')
 old=read(kp)
 for layer in old['kernels']:
  for term in layer['terms']:
   term['coefficient']=[{'port_powers':x['powers'],'integer':x['coefficient']} for x in term['coefficient']]
 need(old==kernels,'exact schema-normalized kernel rebind')
 spath=HERE.parent/'source'/check['source']
 need(sha(spath)==sha(folder/'source.json'),'source copy rebind')
 bindings.append(dict(profile=h,source_sha256=sha(spath),layout_sha256=sha(cp),audited_kernel_sha256=sha(kp),schema_adapted_kernel_sha256=sha(folder/'kernels.json')))
 degrees={d['degree']:max(t['exponent'] for t in d['terms']) for d in kernels['kernels']}; heads={}
 for d in kernels['kernels']:
  for t in d['terms']:need(abs(coefficient(t['coefficient']))<2**2134927,'actual bound')
  heads[d['degree']]=coefficient(max(d['terms'],key=lambda t:t['exponent'])['coefficient'])
 need(max(degrees[d]+d*w for d in degrees)==h,'source height')
 if h==2057:
  need(heads=={0:2*ports[1],1:2,2:ports[0]},'mirror independent positivity')
  need(degrees[1]+w==degrees[2]+2*w==h,'mirror tied leading layers')
  gh=ports[0]+2
 else:
  need(heads[2]==1 and degrees[2]+w-degrees[1]>=3 and degrees[2]+2*w-degrees[0]>=3,'quadratic dominance')
  gh=1
 profiles[h]=(layout,kernels,gh)

def reconstruct(obj,vals,p):
 b,g,h,s,w,C,i,j,n=[vals[z]+(int(obj['domain']=='natural') if z!='j' else -int(obj['domain']=='positive')) for z in obj['variables']]
 Hc=obj['height']; layout,ks,gh=profiles[Hc]; W=max(layout['weights']); Ec=Hc+W+2;Hp=Ec+W+23
 delta=(Hp-15)%2;lp=(22-Hp*2134939)%2;ne=(Hp-15-delta)//2;ce=((15+delta)*2134939+lp-22)//2
 B=pow(2,2134939,p)*b*b%p
 Ds=[sum(coefficient(t['coefficient'],p)*pow(B,t['exponent'],p) for t in row['terms'])%p for row in ks['kernels']]
 ell=sum(pow(B,z,p) for z in layout['weights'])%p;At=sum(pow(B,z,p) for z in layout['targets'])%p
 Us=(ell+g)%p;Gs=(Ds[2]*Us*Us+Ds[1]*Us+Ds[0])%p;N0=pow(B,W+1,p)
 Sc=(g+N0*(2*Gs+At))%p;Tc=(N0-1-(b-1)*ell+N0*(B-2)*At)%p
 L=pow(2,lp,p)*b*pow(B,Ec,p)%p;N=pow(2,ce,p)*pow(b,delta,p)*pow(B,ne,p)%p
 R=(L*(Sc+Tc+1)-Sc-1)%p;t=b*pow(B,W,p)%p
 U=N*N*w%p;Y=N*N*s%p;M=R*Y%p;P=2*M*M*U%p;K=(R+1+h*(P-1))%p;A=M*(U+1)%p
 B1=(2*R+1)%p;W1=b*w%p;J=(4*A-5)%p;Q=(3*W1*C-2*(W1*W1-1))%p
 D=((A*A-1)*C*C+1)%p;k=i*J*C%p;F=(1+k*k*D*D*(D-1))%p;lam=(C*D+1-A)%p
 G=(A+F*lam)%p;Hr=(C+F*(B1+j*C))%p;I=((G*G-1)*Hr*Hr+1)%p
 a0=((P*P-1)*K*K+1)%p;a1=D*F*I%p;V0=P*K%p
 m=(K*K*(4*t-g)-16*t*(C-K*Y)**2)%p
 if obj['refined_majorant']:
  ns=2*G+lam;n1=2*k*k*D*(D-1)*lam+3*C;n2=2*k*k*(D-1)*lam;n3=2*k*k*(lam-C);n4=2*k*k*C
  T=(k*((1024*D*D-512*D-128)*ns-64*n1-40*n2-28*n3-21*n4)+i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048)%p
  V1=T*Hr%p;q=2048**2
 else:T=k*(8*D*D-4*D-1)%p;V1=T*G*Hr%p;q=64
 Om=J*m%p;E0=(J*(n+W1*W1)+Q)%p;Th=(E0-Om*(V0+V1))%p;inner=(Th*Th-Om*Om*(a0+q*a1))%p
 out=(inner*inner-4*q*pow(Om,4,p)*a0*a1)%p
 return dict(B=B,ell=ell,targets=At,Usource=Us,Gsource=Gs,Scode=Sc,Tcode=Tc,L=L,N=N,R=R,capbase=t,U=U,Y=Y,M=M,P=P,K=K,A=A,B1=B1,W1=W1,J=J,Q=Q,D=D,k=k,F=F,Lambda=lam,G=G,H=Hr,I=I,V0=V0,a0=a0,a1=a1,margin=m,Tmajor=T,V1=V1,Omega=Om,E0=E0,Theta=Th,inner=inner,F9=out)
rows=[];rng=random.Random(271828);cases=0
for path in sorted((ROOT/'generated').glob('H*_*.json')):
 obj=read(path);nodes=obj['nodes'];names=obj['variables'];need(len(names)==9 and len(set(names))==9,'nine unknowns')
 need(sha(ROOT/'data'/obj['profile']/'source.json')==obj['source_sha256'],'DAG source binding')
 need(sha(ROOT/'data'/obj['profile']/'layout.json')==obj['layout_sha256'],'DAG layout binding')
 counts=Counter();live={obj['output']}
 for ind,node in reversed(list(enumerate(nodes))):
  if node['kind'] in ['add','sub','mul']:
   need(0<=node['left']<ind and 0<=node['right']<ind,'topological order');counts[node['kind']]+=1
   if ind in live:live.update([node['left'],node['right']])
 need(len(live)==len(nodes),'all DAG nodes live');need(sum(counts.values())==obj['total_operations'] and dict(counts)==obj['operation_counts'],'literal charged operations')
 for rec in obj['coefficient_recipes']:need(coefficient(rec['terms'])==fixed[rec['name']],'exact coefficient recipe')
 Hc=obj['height'];Ec=Hc+118;Hp=Ec+139;delta=(Hp-15)%2;lp=(22-Hp*2134939)%2;ne=(Hp-15-delta)//2;ce=((15+delta)*2134939+lp-22)//2
 need([obj['Ecode'],obj['threshold_b_power'],obj['threshold_B_power'],obj['threshold_scale_exponent'],obj['block_scale_power_of_two']]==[Ec,delta,ne,ce,lp],'calibration parameters')
 for kb in [0,1,2,17,100]:
  v=2134939+2*kb
  need(lp+kb+Ec*v+139*v-31*kb-22==2*(ce+delta*kb+ne*v),'exact parity/popcount calibration')
 for p in [1009,65537,1000003]:
  for trial in range(20):
   vals={name:(0 if obj['domain']=='natural' else 1) if trial==0 else rng.randrange(1,1000) for name in names}
   result=[]
   for nd in nodes:
    kind=nd['kind']
    if kind=='variable':v=vals[nd['name']]
    elif kind=='literal':v=nd['value']
    elif kind=='fixed':v=fixed[nd['name']]
    elif kind=='add':v=result[nd['left']]+result[nd['right']]
    elif kind=='sub':v=result[nd['left']]-result[nd['right']]
    elif kind=='mul':v=result[nd['left']]*result[nd['right']]
    else:raise RuntimeError('unknown node')
    result.append(v%p)
   for name,want in reconstruct(obj,vals,p).items():need(result[obj['named_nodes'][name]]==want%p,'register '+path.name+' '+name)
   cases+=1
 r=4*Ec-1;nu=2*ne+delta;a=r+4*nu+2;omega=5*r+20*nu+233+12;v0=4*r+12*nu+7;v1=23*a+r+29
 if obj['refined_majorant']:
  weighted={e:sum(x*y for x,y in zip(e,[a,1,1])) for e in defect}
  need([e for e,d in weighted.items() if d==max(weighted.values())]==[(15,18,6)],'unique defect weighted leader')
  dd=31*a+2*r+44;expected=86*r+328*nu+4*233+260
 else:dd=40*a+2*r+52;expected=104*r+400*nu+8*116+316
 inn=2*omega+dd
 need(dd>v0+v1 and inn>2*(a+4) and inn>(a+4)+omega+v1,'strict inner degree dominance')
 need(2*inn>4*omega+2*v0+2*v1 and 2*inn==expected,'strict final degree dominance')
 rows.append(dict(file=path.name,sha256=sha(path),operations=sum(counts.values()),degree=expected,domain=obj['domain']))
need(len(rows)==12,'all active variants')
receipt=dict(status='PASS',scope='Independent exact local identities, literal circuit accounting, fixed integers, calibration, source rebinding and modular arithmetic replay; not a new formal proof of inherited compiler/calibration.',cases=cases,defect_terms=len(defect),variants=rows,bindings=bindings,source_audit_sha256=sha(HERE.parent/'carry/VERIFICATION.json'))
(HERE/'INDEPENDENT_NINE_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ['bindings']},indent=2))
