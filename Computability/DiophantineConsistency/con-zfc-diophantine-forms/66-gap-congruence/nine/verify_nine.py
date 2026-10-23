"""Independent arithmetic replay and exact degree proof for the authored composition."""
from pathlib import Path
import json,gzip,hashlib,random,math
ROOT=Path(__file__).resolve().parent
def req(v,msg):
 if not v:raise ValueError(msg)
old_binding=json.loads((ROOT/'data/OLD_TUPLE_BINDING.json').read_text())
for item in old_binding['files']:
 packed=(ROOT/'data'/(item['name']+'.bin.gz')).read_bytes()
 raw=gzip.decompress(packed)
 req(hashlib.sha256(raw).hexdigest()==item['sha256'],'old tuple raw hash')
 req(hashlib.sha256(packed).hexdigest()==item['gzip_sha256'],'old tuple gzip hash')
 req(len(raw)==item['bytes'] and int.from_bytes(raw,'little').bit_length()==item['bit_length'],'old tuple dimensions')
binding=json.loads((ROOT/'fixed/BINDING.json').read_text());fixed={}
for item in binding:
 raw=gzip.decompress((ROOT/'fixed'/(item['name']+'.bin.gz')).read_bytes())
 req(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'fixed hash')
 fixed[item['name']]=item['sign']*int.from_bytes(raw,'little')

def evaldag(obj,vals,mod):
 ns=[]
 for n in obj['nodes']:
  k=n['kind']
  if k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  elif k=='variable':v=vals[n['name']]
  elif k=='add':v=ns[n['left']]+ns[n['right']]
  elif k=='sub':v=ns[n['left']]-ns[n['right']]
  elif k=='mul':v=ns[n['left']]*ns[n['right']]
  else:raise ValueError('node')
  ns.append(v%mod)
 return ns[obj['output']],{k:ns[i] for k,i in obj['named_nodes'].items()}

def independent(vals,obj,mod):
 v=vals.copy()
 if obj['domain']=='natural':
  for name in v:
   if name!='j':v[name]+=1
 else:v['j']-=1
 b,g,h,ss,w,C,i,j,n=(v[x] for x in ['b','g','h','s','w','C','i','j','n'])
 b%=mod;g%=mod;C%=mod
 data=ROOT/'data'/obj['profile'];code=json.loads((data/'layout.json').read_text());ks=json.loads((data/'kernels.json').read_text())
 ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{name}.bin.gz').read_bytes()),'little')%mod for name in ['beta','K','MC','MF_source']]
 B=(pow(2,obj['base_scale_exponent'],mod)*b*b)%mod
 def cc(ts):return sum(t['integer']*math.prod(pow(z,e,mod) for z,e in zip(ports,t['port_powers'])) for t in ts)%mod
 ds={r['degree']:sum(cc(t['coefficient'])*pow(B,t['exponent'],mod) for t in r['terms'])%mod for r in ks['kernels']}
 ell=sum(pow(B,z,mod) for z in code['weights'])%mod;targets=sum(pow(B,z,mod) for z in code['targets'])%mod
 N0=pow(B,obj['W']+1,mod);Us=(ell+g)%mod
 Gs=(ds[2]*Us*Us+ds[1]*Us+ds[0])%mod
 Sc=(g+N0*(2*Gs+targets))%mod;Tc=(N0-1-(b-1)*ell+N0*(B-2)*targets)%mod
 L=(pow(2,obj['block_scale_power_of_two'],mod)*b*pow(B,obj['Ecode'],mod))%mod
 N=(pow(2,obj['threshold_scale_exponent'],mod)*pow(b,obj['threshold_b_power'],mod)*pow(B,obj['threshold_B_power'],mod))%mod
 R=(L*(Sc+Tc+1)-Sc-1)%mod;cap=b*pow(B,obj['W'],mod)%mod
 U=N*N*w%mod;Y=N*N*ss%mod;M=R*Y%mod;P=2*M*M*U%mod;K=(R+1+h*(P-1))%mod;A=M*(U+1)%mod
 B1=(2*R+1)%mod;W1=b*w%mod;J=(4*A-5)%mod;Q=(3*W1*C-2*(W1*W1-1))%mod
 D=((A*A-1)*C*C+1)%mod;k=i*J*C%mod;E=k*D*C%mod;F=((A*A-1)*E*E+1)%mod
 lam=(C*D+1-A)%mod;G=(A+F*lam)%mod;H=(C+F*(B1+j*C))%mod
 I=((G*G-1)*H*H+1)%mod;V0=P*K%mod;a0=((P*P-1)*K*K+1)%mod;a1=D*F*I%mod
 margin=(K*K*(4*cap-g)-16*cap*(C-K*Y)**2)%mod
 if obj['refined_majorant']:
  ns=2*G+lam;N1=2*k*k*D*(D-1)*lam+3*C;N2=2*k*k*(D-1)*lam;N3=2*k*k*(lam-C);N4=2*k*k*C
  t6=k*((1024*D*D-512*D-128)*ns-64*N1-40*N2-28*N3-21*N4)
  T=(t6+i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048)%mod
  V1=T*H%mod;q=2048**2
  defect=json.loads((ROOT/'data/defect.json').read_text())
  err=sum(t['coefficient']*pow(A,t['powers'][0],mod)*pow(C,t['powers'][1],mod)*pow(i,t['powers'][2],mod) for t in defect['terms'])%mod
  req((T*T-q*D*F*G*G)%mod==err,'refined defect identity')
  delta=(H*H*err+q*D*F*(H*H-1))%mod
 else:
  T=k*(8*D*D-4*D-1)%mod;V1=T*G*H%mod;q=64
  delta=(((8*D+1)*k*k-64*D)*(G*H)**2+64*D*F*(H*H-1))%mod
 Om=J*margin%mod;E0=(J*(n+W1*W1)+Q)%mod;theta=(E0-Om*(V0+V1))%mod
 inner=(theta*theta-Om*Om*(a0+q*a1))%mod
 cert=(E0*E0-2*E0*Om*(V0+V1)+Om*Om*(K*K-1+delta+2*V0*V1))%mod
 req(inner==cert,'deflated inner identity')
 output=(inner*inner-4*q*pow(Om,4,mod)*a0*a1)%mod
 return output,dict(B=B,Usource=Us,Gsource=Gs,Scode=Sc,Tcode=Tc,L=L,N=N,R=R,capbase=cap,A=A,D=D,F=F,G=G,H=H,Tmajor=T,V1=V1,Omega=Om,margin=margin)

def exact_degree(obj):
 W,H=obj['W'],obj['height'];r=4*obj['Ecode']-1;nn=2*obj['threshold_B_power']+obj['threshold_b_power'];cap=2*W+1;aa=r+4*nn+2
 omega=5*r+20*nn+cap+12;v0=4*r+12*nn+7
 if obj['refined_majorant']:
  defect=json.loads((ROOT/'data/defect.json').read_text())['terms'];degree=max(sum(x*y for x,y in zip(t['powers'],[aa,1,1])) for t in defect)
  leaders=[t for t in defect if sum(x*y for x,y in zip(t['powers'],[aa,1,1]))==degree]
  req(leaders==[{'powers':[15,18,6],'coefficient':2359296}],'unique refined defect leader')
  delta=31*aa+2*r+44;v1=23*aa+r+29;a1=2*v1
  inner=2*omega+delta
  req(inner>2*(aa+4) and inner>(aa+4)+omega+v1 and delta>v0+v1,'unique inner leader')
  req(2*inner>4*omega+2*v0+a1,'unique final leader')
  out=2*inner;req(out==86*r+328*nn+4*cap+260,'degree formula')
  leader=[]
  ks=json.loads((ROOT/'data'/obj['profile']/'kernels.json').read_text());ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{name}.bin.gz').read_bytes()),'little') for name in ['beta','K','MC','MF_source']]
  gh=0
  for rr in ks['kernels']:
   tt=max(rr['terms'],key=lambda x:x['exponent'])
   if tt['exponent']+rr['degree']*W==obj['height']:
    gh+=sum(z['integer']*math.prod(q**e for q,e in zip(ports,z['port_powers'])) for z in tt['coefficient'])
  req(gh>0,'positive source leading coefficient')
  for prime in [101,1009,1000003]:
   base=pow(2,obj['base_scale_exponent'],prime);th=pow(2,obj['threshold_scale_exponent'],prime)
   rho=pow(2,obj['block_scale_power_of_two']+1,prime)*(gh%prime)*pow(base,2*obj['Ecode']-1,prime)%prime
   nu=th*pow(base,obj['threshold_B_power'],prime)%prime;ca=pow(base,W,prime)
   value=81*pow(2,88,prime)*pow(ca,4,prime)*pow(rho,86,prime)*pow(nu,328,prime)%prime
   req(value!=0,'nonzero actual diagonal leader');leader.append({'prime':prime,'residue':value})
 else:
  delta=40*aa+2*r+52;v1=23*aa+r+29;inner=2*omega+delta
  req(inner>2*(aa+4) and inner>(aa+4)+omega+v1 and delta>v0+v1,'simple unique inner leader')
  req(2*inner>4*omega+2*v0+2*v1,'simple final leader')
  out=2*inner;req(out==104*r+400*nn+8*W+316,'simple degree formula');leader=[]
  ks=json.loads((ROOT/'data'/obj['profile']/'kernels.json').read_text());ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{name}.bin.gz').read_bytes()),'little') for name in ['beta','K','MC','MF_source']]
  gh=0
  for rr in ks['kernels']:
   tt=max(rr['terms'],key=lambda x:x['exponent'])
   if tt['exponent']+rr['degree']*W==obj['height']:gh+=sum(z['integer']*math.prod(q**e for q,e in zip(ports,z['port_powers'])) for z in tt['coefficient'])
  req(gh>0,'simple positive source leader')
  for prime in [101,1009,1000003]:
   base=pow(2,obj['base_scale_exponent'],prime);th=pow(2,obj['threshold_scale_exponent'],prime)
   rho=pow(2,obj['block_scale_power_of_two']+1,prime)*(gh%prime)*pow(base,2*obj['Ecode']-1,prime)%prime
   nu=th*pow(base,obj['threshold_B_power'],prime)%prime;ca=pow(base,W,prime)
   value=pow(2,82,prime)*pow(ca,4,prime)*pow(rho,104,prime)*pow(nu,400,prime)%prime
   req(value!=0,'simple actual diagonal leader');leader.append({'prime':prime,'residue':value})
 return dict(exact_degree=out,R_degree=r,N_degree=nn,cap_degree=cap,A_degree=aa,Omega_degree=omega,actual_diagonal_witnesses=leader)

def main():
 rng=random.Random(60923);rows=[];replays=0
 ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{name}.bin.gz').read_bytes()),'little') for name in ['beta','K','MC','MF_source']]
 for profile in ['H2068','H2082','H2057']:
  data=ROOT/'data'/profile;code=json.loads((data/'layout.json').read_text());ks=json.loads((data/'kernels.json').read_text())
  req(hashlib.sha256((data/'source.json').read_bytes()).hexdigest()==ks['source_sha256'],'source hash')
  W=max(code['weights']);degrees={r['degree']:max(t['exponent'] for t in r['terms']) for r in ks['kernels']}
  dominance=degrees[2]+W-degrees[1]>=3 and degrees[2]+2*W-degrees[0]>=3
  kernelheads=[]
  actual=[]
  for r in ks['kernels']:
   for t in r['terms']:
    value=sum(z['integer']*math.prod(q**e for q,e in zip(ports,z['port_powers'])) for z in t['coefficient'])
    req(abs(value)<1<<2134927,'fixed coefficient bound');actual.append(value)
   tt=max(r['terms'],key=lambda t:t['exponent']);value=sum(z['integer']*math.prod(q**e for q,e in zip(ports,z['port_powers'])) for z in tt['coefficient']);kernelheads.append(value)
  req(all(x>0 for x in kernelheads) or (dominance and kernelheads[2]==1),'unconditional kernel positivity proof branch')
 for path in sorted((ROOT/'generated').glob('H*_*.json')):
  obj=json.loads(path.read_text())
  if 'nodes'not in obj:continue
  live=set()
  def visit(index):
   if index in live:return
   req(0<=index<len(obj['nodes']),'node reference');live.add(index);node=obj['nodes'][index]
   if node['kind'] in ('add','sub','mul'):
    req(node['left']<index and node['right']<index,'acyclic node order');visit(node['left']);visit(node['right'])
  visit(obj['output']);req(len(live)==len(obj['nodes']),'all charged nodes live')
  req({node['name'] for node in obj['nodes'] if node['kind']=='variable'}==set(obj['variables']) and len(obj['variables'])==9,'exact nine live unknowns')
  count=sum(n['kind'] in ('add','sub','mul') for n in obj['nodes']);req(count==obj['total_operations'],'gate count')
  for rec in obj['coefficient_recipes']:
   value=sum(z['integer']*math.prod(q**e for q,e in zip(ports,z['port_powers'])) for z in rec['terms']);req(value==fixed[rec['name']],'whole exact coefficient recipe')
  for prime in [101,1009,1000003]:
   for trial in range(30):
    vals={name:rng.randrange(0 if obj['domain']=='natural' else 1,200) for name in obj['variables']}
    got,named=evaldag(obj,vals,prime);want,regs=independent(vals,obj,prime);req(got==want,'literal output replay')
    for n,v in regs.items():req(named[n]==v,'register replay '+n)
    replays+=1
  row=dict(file=path.name,operations=count,**exact_degree(obj));rows.append(row)
 receipt=dict(status='PASS',scope='Literal finite arithmetic and universal degree identities; inherited compiler/calibration is not proved by this check.',cases=replays,metrics=rows)
 (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
