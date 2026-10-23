if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Fresh independent identities and modular coefficient tests; no upstream code execution."""
import json,random,math,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent
rng=random.Random(20261023)
def evaluate(p,v):
 v=v.copy()
 for n,op,a,b in p['source']:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v

def liveness(p):
 known=set(p['witnesses']+p['fixed_numerals']);seen=[]
 for n,op,a,b in p['source']:
  assert n not in known and op in ['+','-','*'],n
  assert all(isinstance(x,int) or x in known for x in [a,b]),(n,a,b)
  known.add(n)
 live={p['output']} if 'output' in p else {x[0] for x in p['outputs']}
 for n,op,a,b in p['source'][::-1]:
  if n in live:live.update(x for x in [a,b] if isinstance(x,str))
 assert all(n in live for n,*_ in p['source'])
 assert set(p['witnesses']+p['fixed_numerals'])<=live

def ringmul(v,w,A,G):
 z=[0]*4
 for j,a in enumerate(v):
  for k,b in enumerate(w):z[j^k]+=a*b*(A if j&k&1 else 1)*(G if j&k&2 else 1)
 return z

def formula(p,v):
 n=p['variable_count'];small=n==25
 J=v['Jrep' if small else 'J'];z=v['transport_quotient' if small else 'z'];T=v['auxiliary_quotient' if small else 'T'];beta=v['Bm1' if small else 'beta'];K0=v['Kconstant' if small else 'K0']
 F,al,et,ze,s,i,w,h,t=[v[x] for x in ['F','alpha','eta','zeta','s','i','w','h','t']]
 q=beta*J+1;X=w*q;Y=s*q**3;E=X*Y;k=et+ze;c=k*Y+et;a=E+Y;HH=4*a+3;De=a*a+HH;ell=E*k*Y;A=1+ell*(ell+k);G=1+De*c*c;R=((q-1)*(q-F)+al)*(q*q-1)+(v['MC']+q*v['MF'])*J;Nk=k-h*E-R;Nt=(K0+w)*(q-F-al)+q-F-z*(q-1)
 if n==26:
  f=v['f'];gamma=v['gamma'];Nmain=(X+a*c+gamma*HH)**2-De*c*c;Ns=(1+i*i*c**4-De*(f*f-1)) if p.get('ordinary_strong') else (f*f-De*i*i*c**4);Q=De*(f*f-1);d=Q-1;V=c*(T*f-1)-R*f*f;e=Q*V*V-1;U=d*(t*t+A)-e;N=U*U-4*d*d*t*t*A
  return Nmain*Ns*Nk*Nt*(1+N)-1,N
 D=1+De*i*i*c**4;Q=(De*i*c*c)**2;d=Q-1;vv=c*T;b=c+R*D;e=Q*(D*vv*vv+b*b)-1;B=2*Q*vv*b
 if n==25:
  gamma=v['gamma'];Nmain=(X+a*c+gamma*HH)**2-De*c*c;M=i*i*c**4+T*T;C=d*(t*t+M*M*A)-e;U=C*C+D*B*B-4*d*d*t*t*M*M*A;N=U*U-D*(2*C*B)**2
  return Nmain*Nk*Nt*(1+N)-1,N
 W=vv*vv+D+2*b;P=HH*W;K=P+1;u=p.get('separator_multiplier',3)*P;Z=HH*t+K*(X+a*c);out=[1,0,0,0]
 for st in [-1,1]:
  for sg in [-1,1]:
   lin=[Z,-st*u,-sg*K,0];f=[d*x for x in ringmul(lin,lin,A,G)];f[0]-=HH*HH*e;f=ringmul(f,f,A,G);f[0]-=HH**4*B*B*D;out=ringmul(out,f,A,G)
 assert out[1:]==[0,0,0]
 return Nk*Nt*(1+out[0])-1,out[0]

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,P,sign=1):
 z=[0]*max(len(a),len(b))
 for j,x in enumerate(a):z[j]=x
 for j,x in enumerate(b):z[j]=(z[j]+sign*x)%P
 return trim(z)

def mul(a,b,P):
 n=len(a)+len(b)-1;assert min(len(a),len(b))*(P-1)**2<2**64
 aa=int.from_bytes(b''.join(x.to_bytes(8,'little') for x in a),'little');bb=int.from_bytes(b''.join(x.to_bytes(8,'little') for x in b),'little');raw=(aa*bb).to_bytes(8*n,'little')
 return trim([int.from_bytes(raw[i:i+8],'little')%P for i in range(0,len(raw),8)])

def line(p,P,beta,zslope):
 active={'J_positive_a','Jrep_positive_a','h','gamma','f','i_integer','eta_positive_a','w_integer','s_integer'}
 v={x:([0,1] if x in active else [0]) for x in p['witnesses']}
 for x in ['z_positive_a','transport_quotient_positive_a']:
  if x in v:v[x]=[0,zslope]
 v.update({x:[beta if x in ['beta','Bm1'] else 7] for x in p['fixed_numerals']})
 for n,op,a,b in p['source']:
  a=v[a] if isinstance(a,str) else [a%P];b=v[b] if isinstance(b,str) else [b%P]
  v[n]=mul(a,b,P) if op=='*' else add(a,b,P,1 if op=='+' else -1)
 return v[p['output']]
receipts=[]
for path in sorted(H.glob('integer*_degree*.json')):
 p=json.loads(path.read_text());liveness(p);n=p['variable_count'];check=[]
 if 'outputs' in p:continue
 for it in range(120):
  v={x:rng.randrange(-3,4) for x in p['witnesses']};v.update({x:rng.randrange(2,9) for x in p['fixed_numerals']});v=evaluate(p,v);actual,N=formula(p,v);assert actual==v[p['output']],(path,it)
  assert N%4 in [0,1] and v['s']%2==v['i']%2==1 and v['w']>=0
 for P,beta in [(1000003,3),(1000033,5)]:
  a=line(p,P,beta,2);b=line(p,P,beta,0);c=line(p,P,beta,1);diff=add(c,b,P,-1)
  expected=(pow(2,325,P)*pow(beta,785,P) if p.get('separator_multiplier')==2 else pow(2,305,P)*pow(3,8,P)*pow(5,4,P)*pow(beta,789,P) if n==24 else pow(2,111,P)*pow(beta,320,P) if n==25 else pow(2,25,P)*pow(beta,72,P) if p.get('ordinary_strong') else -pow(2,27,P)*pow(beta,80,P))%P
  assert len(a)-1==p['exact_degree'],(path,len(a)-1)
  assert a[-1]==3*expected%P,(n,a[-1],3*expected%P)
  assert len(diff)-1==p['exact_degree'] and diff[-1]==expected,(n,diff[-1],expected)
  check.append({'prime':P,'beta':beta,'degree':len(a)-1,'leading_coefficient':a[-1],'isolated_coefficient':diff[-1]})
 receipts.append({'circuit':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'variables':n,'exact_degree':p['exact_degree'],'ledger':p['ledger'],'all_gates_and_ports_live':True,'independent_signed_formula_checks':120,'modular_degree_checks':check})
 print(path.name,'PASS')
# Exhaustive finite sign/zero-scale checks of the separating bounds, with independent R in its permitted interval.
bounds=0
for q in [16,32]:
 for w in [0,1,4]:
  for s in [-7,-3,-1,1,3,7]:
   for k,eta in [(2,1),(7,3),(30,29)]:
    for i in [-5,-1,1,3]:
     for T in [-7,-1,0,1,4]:
      X=w*q;Y=s*q**3;a=(X+1)*Y;HH=4*a+3;c=k*Y+eta;De=a*a+HH;R=q*(q*q-1)+1;D=1+De*i*i*c**4;Q=(De*i*c*c)**2;b=c+R*D;v=c*T;W=v*v+D+2*b;K=HH*W+1;ell=X*k*Y*Y;A=1+ell*(ell+k);G=1+De*c*c
      assert De>R and 1<b<Q and W>0 and abs(HH)*W>4 and math.gcd(K,HH)==1
      # All exact rational comparisons; no floating-point roots.
      assert 4*K*K*G>4*HH*HH*W*W
      if w:
       assert 4*G<9*A and A>64
       # Sufficient inequalities used in the proof.
       assert 4*abs(K)<5*abs(HH)*W
      bounds+=1
systems=[]
for path in sorted(H.glob('integer*_system*_degree*.json')):
 p=json.loads(path.read_text());liveness(p);norm_output=p['outputs'][-1][0];pp=dict(p,output=norm_output)
 cert=[]
 for P,beta in [(1000003,3),(1000033,5)]:
  a=line(pp,P,beta,2);assert len(a)-1==p['exact_degree']
  cert.append({'prime':P,'beta':beta,'degree':len(a)-1,'leading_coefficient':a[-1]})
 systems.append({'circuit':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'variables':p['variable_count'],'equations':p['equation_count'],'exact_degree':p['exact_degree'],'ledger':p['ledger'],'all_gates_and_ports_live':True,'modular_degree_checks':cert})
 print(path.name,'PASS')
out={'systems':systems,'status':'PASS','circuits':receipts,'signed_bound_and_zero_scale_cases':bounds,'proof_boundary':'Finite circuit/degree/bound diagnostics supplement the unbounded signed Pell and authentic compiler proofs; no accepting run is asserted.'}
(H/'ODD_SCALE_FAMILY_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print('BOUND CASES',bounds)
