#!/usr/bin/env python3
"""Independent exact circuit audit plus explicitly finite arithmetic diagnostics.
No construction builder/auditor is imported. Checks survive Python -O.
"""
import ast,gzip,hashlib,itertools,json,math,sys,time
from collections import Counter
from pathlib import Path
from sympy import ZZ,discriminant,Symbol
from sympy.polys.rings import ring
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
start=time.monotonic();P=1000000007
receipt={'status':'RUNNING','optimized':not __debug__,'checks':{},'diagnostics':{},'negative_controls':{}}
def req(c,m):
 if not c:raise ValueError(m)
def eq(a,b,m):req(a==b,m)
def rm(names):
 r=ring(','.join(names),ZZ);return r[0],dict(zip(names,r[1:]))
def parse(s,e):
 def f(n):
  if isinstance(n,ast.Name):return e[n.id]
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return n.value
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -f(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=f(n.left),f(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Pow):return a**b
  raise ValueError(ast.dump(n))
 return f(ast.parse(s,mode='eval').body)
# Generic full norm: each conjugation doubles the number of literal sign factors.
r,x,*roots=ring('x,r0,r1,r2,r3,r4',ZZ);norm=x-sum(roots,r.zero)
for i in range(5):
 norm*=r.from_dict({m:c*(-1 if m[i+1]%2 else 1) for m,c in norm.items()})
req(all(all(k%2==0 for k in m[1:]) for m in norm),'norm sign invariance')
R,e=rm(['x','a0','a1','a2','a3','a4'])
expected=R.from_dict({(m[0],)+(tuple(k//2 for k in m[1:])):v for m,v in norm.items()})
receipt['checks']['full_norm_coefficient_count']=len(expected)
forms={
 'J':'1+6*j','q':'1+beta*J','W0':'4*(3*w+1)','X':'q*W0','Y':'q**3*(1+2*v)',
 'E':'X*Y','a':'E+Y','H':'3+4*a','Delta':'a*a+H','F':'K0*C+W0*C-z*q+z',
 'R':'(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J','k':'1+R+h*E','eta':'c-Y*k',
 'U':'cone_A*F','Zc':'cone_B*C','Derr':'U*U+Zc*Zc-2*q*(U+Zc)+2*q*q',
 'Budget':'(q*k)**2-k*k*Derr-(2*q*eta)**2','Dg':'1+4*(3*Budget-4)*s*s',
 'I':'2*s*r*c*c','I2':'I*I','Df':'1+Delta*I2','Q':'Delta*Delta*I2','delta':'Q-1',
 'V':'Df*c-Df*R+4*Df*I*T-c','Cy':'Q*V*V-1','Da':'delta*Cy',
 'ell':'E*Y','Ltau':'ell*k','Dt':'1+Ltau*Ltau+Ltau*k','Dm':'1+Delta*c*c','b0':'X+a*c',
 'u':'H*T-b0','u2':'u*u','H2':'H*H','H3':'H*H2','Q0':'u2+Dm+31*H2',
 'C0':'u*(u2+3*Dm+H2)+H3','C1':'3*u2+Dm+H2','u_twice':'2*u',
 'A':'u**5+10*u**3*Dm+5*u*Dm**2+32*H**2*(u**3+3*u*Dm)+H**3*(u*u+Dm)+31*H**4*u+31*H**5',
 'B':'5*u**4+10*u*u*Dm+Dm*Dm+32*H**2*(3*u*u+Dm)+2*H**3*u+31*H**4',
 'H5':'H**5','S':'I*H5','S2':'S*S','A0':'B*B*Dm','A1':'4*S2*Da','A2':'S2*Df','A3':'16*S2*Dt','A4':'64*S2*Dg',
 'aux_shift':'(2*Q-1)*V','tau_shift':'4*Ltau'
}
files=[ROOT/'eleven'/f'budget_intersective11_degree{d}.json' for d in [2912,2272,2240]]
pinned={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
packets=[]
for fp in files:
 p=json.loads(fp.read_text());packets.append(p);nr=p['named_registers'];nodes=p['nodes'];variant=p['centering_variant']
 fs=forms|{'center':{'direct':'S*n-A','aux':'S*(n+aux_shift)-A','both':'S*(n+aux_shift+tau_shift)-A'}[variant]}
 names=list(dict.fromkeys(p['variables']+['beta','K0','MC','MF','cone_A','cone_B']+list(fs)));rr,env=rm(names)
 cut_count=0
 for target,fo in fs.items():
  if target not in nr:continue
  deps={n.id for n in ast.walk(ast.parse(fo,mode='eval')) if isinstance(n,ast.Name)}
  cuts={nr[n]:env[n] for n in deps if n in nr};cache={}
  def walk(i):
   if i in cuts:return cuts[i]
   if i in cache:return cache[i]
   nd=nodes[i];op=nd[0]
   if op=='integer':v=rr(nd[1])
   elif op in ('variable','coefficient'):v=env[nd[1]]
   else:
    a,b=walk(nd[1]),walk(nd[2]);v=a+b if op=='add' else a-b if op=='sub' else a*b
   cache[i]=v;return v
  eq(walk(nr[target]),parse(fo,env),fp.name+' front '+target);cut_count+=1
 cuts={nr['center']:e['x']}|{nr[f'A{i}']:e[f'a{i}'] for i in range(5)};cache={}
 def nw(i):
  if i in cuts:return cuts[i]
  if i in cache:return cache[i]
  nd=nodes[i]
  if nd[0]=='integer':v=R(nd[1])
  else:
   req(nd[0] in ('add','sub','mul'),'uncut norm leaf');a,b=nw(nd[1]),nw(nd[2]);v=a+b if nd[0]=='add' else a-b if nd[0]=='sub' else a*b
  cache[i]=v;return v
 eq(nw(p['output']),expected,fp.name+' full exact norm')
 seen=set();degrees=[]
 def visit(i):
  if i in seen:return
  seen.add(i);nd=nodes[i];op=nd[0]
  if op in ('add','sub','mul'):
   req(0<=nd[1]<i and 0<=nd[2]<i,'acyclic');visit(nd[1]);visit(nd[2])
  else:req(op in ('variable','coefficient','integer'),'gate syntax')
 visit(p['output']);eq(seen,set(range(len(nodes))),'all nodes live')
 counts=dict(Counter(nd[0] for nd in nodes if nd[0] in ('add','sub','mul')))
 eq(counts,p['operation_counts'],'gate census');eq(sum(counts.values()),p['operations'],'gate total')
 eq(set(nd[1] for nd in nodes if nd[0]=='variable'),set(p['variables']),'input leaves');eq(len(p['variables']),11,'eleven coordinates')
 for nd in nodes:
  op=nd[0];degrees.append(1 if op=='variable' else 0 if op in ('integer','coefficient') else degrees[nd[1]]+degrees[nd[2]] if op=='mul' else max(degrees[nd[1]],degrees[nd[2]]))
 rad=[degrees[nr[f'A{i}']] for i in range(5)];eq(rad,[70,182,88,102,94],'radicand degrees')
 receipt['checks'][p['name']]={'front_cuts':cut_count,'operations':sum(counts.values()),'counts':counts,'radicand_degrees':rad}
# Exact generic local identities for the degree filtration and Pell/quintic proof.
r,e=rm(['S','Q','V','L','k','H','u','D','c','I','R','T','delta','s','jaux','rr'])
S,Q,V,L,k,H,u,D,c,I,R0,T,delta,s,jaux,rr=(e[n] for n in e)
eq(4*S*S*(Q-1)*(Q*V*V-1)-(S*(2*Q-1)*V)**2,S*S*(-V*V-4*Q+4),'auxiliary deviation identity')
eq(16*S*S*(1+L*(L+k))-(4*S*L)**2,16*S*S*(1+L*k),'tau deviation identity')
f2=1+D*I*I;VV=f2*(c-R0+4*I*T)-c
eq(VV+R0,D*I*I*(c-R0)+4*I*f2*T,'auxiliary congruences')
Vp=(2*Q-1)*V-2*(Q-1)*c;yp=(2*Q-1)*c-2*Q*V
eq(Q*Vp*Vp-(Q-1)*yp*yp,Q*V*V-(Q-1)*c*c,'adjacent Pell descent')
BB=5*u**4+10*u*u*D+D*D+32*H*H*(3*u*u+D)+2*H**3*u+31*H**4
cert=5*u**4+10*u*u*D+D*D+32*H*H*D+95*H*H*u*u+H*H*(u+H)**2+30*H**4
eq(BB,cert,'strict positivity certificate')
xx=Symbol('x');eq(discriminant(xx**3+xx+1,xx),-31,'cubic discriminant')
receipt['checks']['exact_generic_proof_identities']=6
# Authenticate every copied dependency and pin the actual mathematical note.
proof=ROOT/'eleven/PROOF.md'
pinned[str(proof.relative_to(ROOT))]=hashlib.sha256(proof.read_bytes()).hexdigest()
source_pins=json.loads((ROOT/'eleven/SOURCE_PINS.json').read_text())['sources']
for pin in source_pins:
 raw=(ROOT/'eleven'/pin['path']).read_bytes()
 eq(hashlib.sha256(raw).hexdigest(),pin['sha256'],'source hash '+pin['path'])
 eq(len(raw),pin['bytes'],'source bytes '+pin['path'])
receipt['checks']['authenticated_source_pins']=len(source_pins)
# Authentic coefficient bytes and exact degree lower bounds on an independent line.
binding=json.loads((ROOT/'guard/coefficients/BINDING.json').read_text());ports={}
for name,it in binding['payloads'].items():
 raw=gzip.decompress((ROOT/'guard/coefficients'/it['file']).read_bytes());eq(hashlib.sha256(raw).hexdigest(),it['raw_sha256'],'payload '+name);ports[name]=int.from_bytes(raw,'little')%P
 for sub in ['centered17','centered18']:
  eq(raw,gzip.decompress((ROOT/'guard/provenance'/sub/'coefficients'/it['file']).read_bytes()),'same source tuple')
for p in packets:
 d=p['exact_degree'];slopes={nm:13+11*i+7*i*i for i,nm in enumerate(p['variables'])}
 def ev(t):
  ee=ports|{n:a*t%P for n,a in slopes.items()};vs=[]
  for nd in p['nodes']:
   op=nd[0]
   if op=='integer':z=nd[1]
   elif op in ('variable','coefficient'):z=ee[nd[1]]
   else:
    a,b=vs[nd[1]],vs[nd[2]];z=a+b if op=='add' else a-b if op=='sub' else a*b
   vs.append(z%P)
  return vs[p['output']]
 row=[ev(t) for t in range(d+1)]
 for _ in range(d):row=[(b-a)%P for a,b in zip(row,row[1:])]
 lc=row[0]*pow(math.factorial(d)%P,-1,P)%P;req(lc!=0,'degree lower bound '+str(d))
 receipt['checks'][p['name']]['degree']={'degree':d,'leading_coefficient_mod_prime':lc,'prime':P,'line_slopes':slopes,'upper_bound_method':('unique degree182 radicand' if d==2912 else 'Laurent auxiliary correction degree27; 16*91+16*51' if d==2272 else 'Laurent auxiliary/tau corrections degree27/41; 16*91+8*51+8*47'),'lower_bound_method':'exact finite differences on fixed-coefficient line'}
# An independent closed-form coefficient check from the Laurent sign grouping.
r0,z=rm(['j','w','v','h','s','rr','c','T','beta'])
j,w,v,h,s,rr,c,T,beta=(z[n] for n in z)
q0=6*beta*j;Y0=2*v*q0**3;a0=q0*(12*w)*Y0;I0=2*s*rr*c*c
S0=I0*(4*a0)**5;Q0=a0**4*I0**2;Vsel=a0*a0*I0**2*(4*I0*T)
Lt0=h*a0*a0*Y0;Dg0=-48*q0*q0*Y0*Y0*h*h*a0*a0*s*s
selected=(4*S0*Q0*Vsel)**16*(8*S0*Lt0)**8*(64*S0*S0*Dg0)**4
exponents=(1176,280,296,16,120,112,224,16,1176)
eq(dict(selected),{exponents:2**2592*3**1460},'independent exact2240 coefficient')
receipt['checks']['exact2240_selected_coefficient']={'exponents':dict(zip(['j','w','v','h','s','r','c','T'],exponents[:8])),'coefficient':'2^2592 * 3^1460 * beta^1176','method':'independent Laurent sign grouping; maximal T chooses each 4I0T'}
# Pell modular arithmetic uses binary exponentiation, not author routines.
def pell(a,n,mod=None):
 D=a*a-1
 def mul(x,y):
  z=(x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0]);return tuple(t%mod for t in z) if mod else z
 x=(1,0);b=(a,1)
 while n:
  if n&1:x=mul(x,b)
  b=mul(b,b);n//=2
 return x
def crt(a,m,b,n):
 g=math.gcd(m,n);req((b-a)%g==0,'CRT compatible');return (a+m*((b-a)//g*pow(m//g,-1,n//g)%(n//g)))%(m*(n//g))
residue_cases=[]
for n0,N in [(90,1),(180,2)]:
 A=2;Delta=A*A-1;rank=3;c0=pell(A,rank)[1];f,I0=pell(A,n0)
 eq(I0%(4*N*c0*c0),0,'strong requested modulus');lam=4*n0*f
 eq(pell(A,lam,f*f),(1,0),'corrected period');req((4*I0)%math.gcd(lam,4*I0*I0)==0,'CRT gcd lemma')
 for av in [0,1,2,7,-1,I0-1]:
  L0=crt(rank,lam,rank-4*I0*av,4*I0*I0)
  if not L0:L0=math.lcm(lam,4*I0*I0)
  eq(L0%4,3,'odd auxiliary index');rho=Delta*I0;M=4*I0*I0*f*f
  chi_mod,_=pell(rho,L0,rho*M);eq(chi_mod%rho,0,'odd quotient');Vmod=chi_mod//rho
  num=(Vmod+c0-f*f*(c0-rank))%M;den=4*I0*f*f
  eq(num%den,0,'integral interpolation quotient');eq((num//den)%I0,av%I0,'full residue')
 residue_cases.append({'A':A,'R':rank,'n0':n0,'N':N,'residues_checked':6,'I_digits':len(str(I0))})
receipt['diagnostics']['full_residue_interpolation']=residue_cases
# Finite residue tests supplement, not prove, the unbounded arguments.
def pi(x):return (x*x+31)*(x*x*x+x+1)
for m in range(1,513):req(any(pi(x)%m==0 for x in range(m)),'intersective sample '+str(m))
receipt['diagnostics']['intersective_moduli']='all 1 through 512'
for A in [2,4,6,8]:
 for n0 in range(1,41):
  _,v=pell(A,n0)
  for prime in [2,3,5,7,11,13,17,19]:
   if v%prime:continue
   def vp(x):
    z=0
    while x%prime==0:z+=1;x//=prime
    return z
   req(vp(v)>=vp(n0),'valuation diagnostic')
receipt['diagnostics']['valuation_samples']='A=2,4,6,8; n=1..40; primes through19'
# Negative controls explicitly falsify relaxed shortcuts, not the full equation.
eq(pell(2,8,49),(1,35),'bad-period counterexample');eq(pell(2,56,49),(1,0),'corrected-period witness')
receipt['negative_controls']={
 'period_4n_is_false':{'A':2,'n':2,'f':7,'alpha_power_8_mod49':[1,35],'alpha_power_56_mod49':[1,0]},
 'even_radicands_break_parity':'sqrt(8)-2sqrt(2)=0: distinct power-of-two weights alone are insufficient.',
 'repeated_two_adic_weight_breaks_parity':'sqrt(18)-3sqrt(2)=0 with odd radicands; distinct weight valuations matter.',
 'main_root_must_be_removed':'sqrt(2)-sqrt(2)=0 shows why the unweighted main radical cannot join the four parity-separated roots without its projection argument.',
 'cubic_alone_not_intersective':'x^3+x+1 has no root modulo2.',
 'disk_does_not_imply_determinant':{'q':100,'U':190,'Zc':100,'disk_error':8100,'determinant':-17100},
 'even_guard_excludes_budget_one':'For Budget=1, g^2+4s^2=1 has no solution with s nonzero. Completeness uses canonical Budget>1.',
 'arbitrary_pell_coefficients_fail_integrality':'5*1^2-16*(1/2)^2=1.',
 'odd_source_coordinate_cannot_be_reused':'Delta=3 and I/c^2=2 give (Delta*I/c^2-1)/2=5/2, not an integer. Fresh odd witnesses are required.'
}
# Verify the indicated controls as arithmetic, not just prose.
eq(8,4*2,'even control');eq(18,9*2,'weight control');eq([((x**3+x+1)%2) for x in [0,1]],[1,1],'cubic mod2');req(8100<10000 and 190*100-(100-190-100)**2<0,'disk control')
for rel,hsh in pinned.items():eq(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest(),hsh,'input changed during audit')
receipt['files_sha256']=pinned
receipt['scope']='Exact finite algebra and metrics plus finite arithmetic diagnostics. Universal signed reduction, interpolation, and inherited native/compiler calibration are separately reviewed in REVIEW.md; no formal-kernel certificate is claimed.'
receipt['status']='PASS';receipt['seconds']=round(time.monotonic()-start,3)
(OUT/('RECEIPT_OPTIMIZED.json' if sys.flags.optimize else 'RECEIPT_NORMAL.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
