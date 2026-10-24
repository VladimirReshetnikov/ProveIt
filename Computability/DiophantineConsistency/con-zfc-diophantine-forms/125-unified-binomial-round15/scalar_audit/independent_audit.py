#!/usr/bin/env python3
"""Independent round-15 audit. Does not import any producer module.
The proof review is SEMANTIC_AUDIT.md; these exact checks bind its equation.
"""
from pathlib import Path
import argparse, collections, copy, gzip, hashlib, itertools, json, sys
import sympy as sp
HERE=Path(__file__).resolve().parent
BASE=HERE.parent
VARS='j C z h r v w T c n s'.split()
PORTS='beta K0 MC MF cone_A cone_B'.split()
PIN={
'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
'K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
'MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
'cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
'cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}

def require(ok,msg):
 if not ok: raise ValueError(msg)

def payloads(directory):
 binding=json.loads((directory/'BINDING.json').read_text());out={}
 require(binding['tuple']=='mixed-parity-unrounded-1064921','wrong tuple')
 require(binding['MF_convention']=='MF_native + beta, already shifted','wrong MF convention')
 for name in PORTS:
  e=binding['payloads'][name];raw=gzip.decompress((directory/e['file']).read_bytes())
  require(hashlib.sha256(raw).hexdigest()==PIN[name]==e['raw_sha256'],'payload hash '+name)
  value=int.from_bytes(raw,'little');require(value.bit_length()==e['bits'],'payload bit length')
  require(len(raw)==e['raw_bytes'] and raw[-1]!=0,'nonminimal payload')
  out[name]=value
 require(out['beta']==2**1064921-1,'beta recipe')
 require(out['cone_A']==2**1113 and out['cone_B']==2**666104,'cone recipes')
 require(out['beta']%6==1 and out['cone_A']%4==out['cone_B']%4==0,'bootstrap residues')
 return out

def formulas(centered,expanded,paired=False,weak=False):
 # Independent mathematical transcription; explicit source cuts avoid giant expansion.
 f={
 'J':'6*j+1','qm':'beta*J','q':'qm+1','q2':'q*q','q3':'q2*q',
 'W':'12*w+4','X':'q*W','Y':'(2*v+1)*q3','Eprod':'X*Y','a':'Eprod+Y','H':'4*a+3','Delta':'a*a+H',
 'F':'(K0+W)*C-z*qm','R':'(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J',
 'k':'R+1+h*Eprod','c2':'c*c','eta':'c-Y*k',
 'Derr':'(cone_A*F-q)**2+(cone_B*C-q)**2','Budget':'k*k*(q2-Derr)-4*q2*eta*eta',
 'ell':'Eprod*Y','L':'ell*k','Dt':'1+L*(L+k)','D':'3*Budget-4','Dg':'1+D*Dt*s*s','P':'Dt*Dg',
 'I':'r*c2','strong':'Delta*I*I','Df':'strong+1','Q':'Delta*strong','delta':'Q-1',
 'b0':'c-R+4*I*T','V':'Df*b0-c','Cy':'Q*V*V-1','K':'X*(3*c-2*X)+2',
 'H2':'H*H','H3':'H2*H','S':'s*r*H','S2':'S*S','zc':'H*T+K','zc2':'zc*zc',
 'Ac':'(zc2+3*H2)*(zc2*zc-19*H3)'}
 if paired:
  del f['D'];del f['Dg'];del f['P']
  f['D81']='243*Budget-324';f['Dg81']='81+D81*Dt*s*s';f['P81']='Dt*Dg81'
 if weak:
  del f['q3'];f['Y']='q*v'
  for name in ['H2','H3','S','S2','zc','zc2','Ac']:del f[name]
  f.update({'M':'2*q2','Dcar':'H*M','M2':'M*M','M4':'M2*M2','Dcar2':'Dcar*Dcar','Dcar3':'Dcar2*Dcar','S':'s*r*Dcar*M4','S2':'S*S','zc':'Dcar*T+M*K+H*(v-q2)','zc2':'zc*zc','Ac':'(zc2+3*Dcar2)*(zc2*zc-19*Dcar3)'})
 if centered:f['shift']='Q*V'
 f.update({'Z':'S*(n+shift)-Ac' if centered else 'S*n-Ac','Z2':'Z*Z',
 'A':'9*S2*Df','B':'S2*delta*Cy','G':'S2*P81' if paired else '81*S2*P'})
 if expanded:
  f.update({'W0':'S*n-Ac','center0':'S*Q*V','omega':'W0*W0+2*center0*W0+S2*(Q*(V*V+1)-1)',
  'vnorm':'omega-A-G','AG':'A+G','ynorm':'vnorm*vnorm-4*(A*G+B*AG)',
  'output':'ynorm*ynorm-64*A*B*G*Z2'})
 elif paired:
  f.update({'vnorm':'Z2+A-B-G','left':'A*Z2','right':'B*G','ynorm':'vnorm*vnorm-4*(left+right)','output':'ynorm*ynorm-64*left*right'})
 else:
  f.update({'AB':'A+B','prod':'A*B','vnorm':'Z2-AB-G','ynorm':'vnorm*vnorm-4*(prod+G*AB)',
  'output':'ynorm*ynorm-64*prod*G*Z2'})
 return f

def graph_check(packet,weak=False):
 require(packet['variables']==VARS and packet['variable_count']==11,'variable list')
 require(packet['domain']=='unrestricted integers','domain')
 nodes=packet['nodes'];regs=packet['named_registers'];out=packet['output'];counts=collections.Counter()
 degrees=[];live=set()
 for i,row in enumerate(nodes):
  op=row[0]
  if op in ['add','sub','mul']:
   require(len(row)==3 and all(isinstance(x,int) and 0<=x<i for x in row[1:]),'topology')
   counts[op]+=1;degrees.append(degrees[row[1]]+degrees[row[2]] if op=='mul' else max(degrees[row[1]],degrees[row[2]]))
  elif op=='integer':require(len(row)==2 and type(row[1])==int,'integer leaf');degrees.append(0)
  elif op=='variable':require(row[1] in VARS,'unknown variable');degrees.append(1)
  elif op=='coefficient':require(row[1] in PORTS,'unknown coefficient');degrees.append(0)
  else:raise ValueError('forbidden operation')
 def mark(i):
  if i in live:return
  live.add(i)
  if nodes[i][0] in ['add','sub','mul']:
   mark(nodes[i][1]);mark(nodes[i][2])
 mark(out)
 require(live==set(range(len(nodes))),'dead nodes')
 require(set(r[1] for r in nodes if r[0]=='variable')==set(VARS),'missing variable')
 require(set(r[1] for r in nodes if r[0]=='coefficient')==set(PORTS),'missing port')
 require(dict(counts)==packet['operation_counts'] and sum(counts.values())==packet['operations'],'operation count')
 require(degrees[out]==packet['syntactic_degree_bound'],'syntactic degree')
 centered=packet['description']['center'];expanded=packet['description']['norm_schedule']=='centered'
 require(not packet['description']['rational'],'not the audited integral equation')
 require(packet['exact_degree']==((416 if centered else 456) if weak else (464 if centered else 488)),'claimed exact degree')
 forms=formulas(centered,expanded,packet['description']['norm_schedule']=='paired',weak)
 syms={k:sp.Symbol(k) for k in list(forms)+VARS+PORTS};cuts={}
 for i,row in enumerate(nodes):
  if row[0] in ['variable','coefficient']:cuts[i]=syms[row[1]]
 def expression(i,root=False):
  if i in cuts and not root:return cuts[i]
  row=nodes[i];op=row[0]
  if op=='integer':return sp.Integer(row[1])
  if op in ['variable','coefficient']:return syms[row[1]]
  aa,bb=expression(row[1]),expression(row[2])
  return aa+bb if op=='add' else aa-bb if op=='sub' else aa*bb
 for name,formula in forms.items():
  require(name in regs,'missing register '+name)
  actual=expression(regs[name],True);want=sp.sympify(formula,locals=syms)
  require(sp.expand(actual-want)==0,'register identity '+name)
  cuts[regs[name]]=syms[name]
 require(regs['output']==out,'output cut')
 require(set(regs)<=set(forms)|set(VARS),'unrecognized exported mathematical cut')
 return {'operations':sum(counts.values()),'operation_counts':dict(counts), 'syntactic_degree_bound':degrees[out], 'verified_registers':len(forms)}

def norm_identity():
 z,a,b,e=sp.symbols('z a b e');r1,r2,r3=sp.symbols('r1 r2 r3')
 full=sp.Poly(sp.prod(z-i*r1-j*r2-k*r3 for i,j,k in itertools.product([-1,1],repeat=3)),z,r1,r2,r3)
 coeff={}
 for exp,c in full.terms():
  require(all(x%2==0 for x in exp[1:]),'odd root power')
  coeff[(exp[0],exp[1]//2,exp[2]//2,exp[3]//2)]=c
 product=sum(c*z**i*a**j*b**k*e**l for (i,j,k,l),c in coeff.items())
 formula=((z*z-a-b-e)**2-4*(a*b+a*e+b*e))**2-64*a*b*e*z*z
 require(sp.expand(formula-product)==0,'complete universal norm')
 paired=((z*z+a-b-e)**2-4*(a*z*z+b*e))**2-64*a*z*z*b*e
 require(sp.expand(formula-paired)==0,'paired universal norm')
 budget,dt,s=sp.symbols('budget dt s')
 require(sp.expand(dt*(81+(243*budget-324)*dt*s*s)-81*dt*(1+(3*budget-4)*dt*s*s))==0,'weighted guard identity')
 W,L,D=sp.symbols('W L D')
 centered=((W*W+2*L*W+D-a-e)**2-4*(a*e+(L*L-D)*(a+e)))**2-64*a*(L*L-D)*e*(W+L)**2
 require(sp.expand(formula.subs({z:W+L,b:L*L-D})-centered)==0,'universal centering')
 ss,qq,vv=sp.symbols('ss qq vv')
 require(sp.expand((ss*qq*vv)**2-ss**2*(qq-1)*(qq*vv**2-1)-ss**2*(qq*(vv**2+1)-1))==0,'source centering cut')
 return {'full_norm_monomials':len(coeff),'full_norm_identity':True,'paired_norm_identity':True,'weighted_guard_identity':True,'universal_centering_identity':True,'source_centering_identity':True}

def poly_eval(packet,values,prime=1000003,weak=False):
 # Exact univariate substitution x_i=t over F_p. Nonzero top coefficient is
 # a rigorous authentic-specialization lower bound, not a random degree guess.
 def add(a,b,minus=False):
  c=[0]*max(len(a),len(b))
  for i,x in enumerate(a):c[i]=x
  for i,x in enumerate(b):c[i]=(c[i]-x if minus else c[i]+x)%prime
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  c=[x%prime for x in c]
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 result=[]
 for row in packet['nodes']:
  op=row[0]
  if op=='variable':x=[0,1]
  elif op=='coefficient':x=[values[row[1]]%prime]
  elif op=='integer':x=[row[1]%prime]
  elif op=='mul':x=mul(result[row[1]],result[row[2]])
  else:x=add(result[row[1]],result[row[2]],op=='sub')
  result.append(x)
 final=result[packet['output']]
 expected=(416 if packet['description']['center'] else 456) if weak else (464 if packet['description']['center'] else 488)
 require(len(final)-1==expected,'authentic specialization lower bound')
 return {'prime':prime,'substitution':'Every variable equals t; actual coefficient payloads reduced modulo p.', 'degree':len(final)-1,'leading_coefficient':final[-1]}

def mutations(packet,weak=False):
 mutations=[]
 def reject(label,change):
  p=copy.deepcopy(packet);change(p)
  counts=collections.Counter(r[0] for r in p['nodes'] if r[0] in ['add','sub','mul']);p['operation_counts']=dict(counts);p['operations']=sum(counts.values())
  deg=[]
  for r in p['nodes']:deg.append((deg[r[1]]+deg[r[2]] if r[0]=='mul' else max(deg[r[1]],deg[r[2]])) if r[0] in ['add','sub','mul'] else int(r[0]=='variable'))
  p['syntactic_degree_bound']=deg[p['output']]
  try:graph_check(p,weak)
  except ValueError as e:mutations.append({'name':label,'rejected':True,'reason':str(e)});return
  raise ValueError('mutation accepted: '+label)
 reject('final norm minus changed to plus',lambda p:p['nodes'][p['output']].__setitem__(0,'add'))
 reject('I changes r to c',lambda p:p['nodes'][p['named_registers']['I']].__setitem__(1,p['named_registers']['c']))
 reject('carrier constant sign changed',lambda p:p['nodes'][p['named_registers']['K']].__setitem__(0,'sub'))
 reject('fusion guard sign changed',lambda p:p['nodes'][p['named_registers']['Dg81']].__setitem__(0,'sub'))
 reject('three-adic coefficient 9 becomes 1',lambda p:next(r for r in p['nodes'] if r==['integer',9]).__setitem__(1,1))
 reject('center QV becomes Q+V',lambda p:p['nodes'][p['named_registers']['shift']].__setitem__(0,'add'))
 return mutations

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--norm-dir',type=Path,default=BASE/'norm');ap.add_argument('--out',type=Path,default=HERE/'AUDIT_RESULTS.json');a=ap.parse_args()
 coeffdir=a.norm_dir/'coefficients'
 if not coeffdir.exists():coeffdir=BASE/'scalar'/'coefficients'
 vals=payloads(coeffdir);result={'auditor':'independent_audit.py; no producer executable imports','coefficient_payloads':PIN,'identities':norm_identity(),'graphs':{}}
 for name in ['integral_direct','integral_centered','integral_centered_expandedcut','integral_direct_paired','integral_centered_paired']:
  path=a.norm_dir/(name+'.json');p=json.loads(path.read_text());row=graph_check(p);row['sha256']=hashlib.sha256(path.read_bytes()).hexdigest();row['authentic_degree_lower_bound']=poly_eval(p,vals);result['graphs'][name]=row
  if name=='integral_centered_paired':result['mutation_controls']=mutations(p)
 require(result['graphs']['integral_centered_expandedcut']['syntactic_degree_bound']==464,'center upper bound')
 result['exact_degree_certification']='Universal paired-norm and centering identities bind the 119-gate centered graph to the expanded-cut graph with upper bound 464; nonzero authentic finite-field leading coefficient proves lower bound 464. The direct graph has syntactic upper bound 488 and matching lower bound.'
 result['semantic_review']='SEMANTIC_AUDIT.md';result['status']='PASS'
 a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
