#!/usr/bin/env python3
"""Independent arithmetic fixtures, sparse expansion checks and clean replay."""
import argparse, collections, hashlib, importlib.util, itertools, json, math, pathlib, subprocess, sys, tempfile
ROOT=pathlib.Path(__file__).resolve().parent

def need(ok,msg):
 if not ok:raise ValueError(msg)
def pell(a,k):
 x,y=1,0
 for _ in range(k):x,y=a*x+(a*a-1)*y,x+a*y
 return x,y

def primes(n):
 out=[];p=2
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p+=1
 if n>1:out.append(n)
 return out

def arithmetic_fixtures():
 counters=collections.Counter()
 for m in range(11):
  M=math.factorial(max(m-1,0))
  for a,b in itertools.combinations(range(1,m+1),2):
   need(math.gcd(1+a*M,1+b*M)==1,'factorial separation');counters['coprimality_pairs']+=1
 for M in range(1,101):need(1+(M+2)*M==(M+1)**2,'fixed-base counterexample')
 counters['fixed_base_counterexamples']=100
 for K in range(4,9):
  T=math.factorial(K)
  for N in range(0,min(K,6)+1):
   ds=[j*T-1 for j in range(1,N+1)];B=math.prod(ds)
   for d in ds:
    ps=primes(d);need(d%4==3 and any(p%4==3 for p in ps),'negative-modulus nonsquare prime')
    need(all(p>K for p in ps),'factorial prime lift')
   need(all(math.gcd(a,b)==1 for a,b in itertools.combinations(ds,2)),'CRT coprimality')
   Q=(1+(N+1)*T)**N+2;L=T*Q+1
   numerator=T**N*math.factorial(N)*math.comb(Q+N,N)
   need(B<Q<L and numerator%L==B,'negative modulus product identity');counters['moduli_product_cases']+=1
 for p in [3,7,11,19,23,31,43]:
  for a in range(p):
   for b in range(p):need(((a*a+b*b)%p==0)==(a==b==0),'binary norm zero')
   counters['norm_field_cases']+=p
 need((1+4)%5==0 and (1+1+1)%3==0,'norm negative controls')
 for n in range(1,8):
  for A in range(max(2,n),11):
   for k in range(13):
    X,Y=pell(A,k);F=X-(A-n)*Y
    need(F>=n**k,'power forward inequality')
    if k:
     T=2*A*n-n*n-1
     if T>0:need((F-n**k)%T==0,'power congruence recurrence')
    counters['power_orientation_cases']+=1
 for A in range(2,7):
  for k in range(1,4):
   X,Y=pell(A,k);h=2*k*Y;U,V=pell(A,h)
   need(U>A and V>0 and V%(Y*Y)==0 and math.gcd(U,4*Y)==1,'canonical Pell auxiliary')
   qb=((1-A)*pow(U,-1,4*Y))%(4*Y);B=A+U*qb
   S,R=pell(B,k)
   need(B>=A and S>=X and R>=k,'simultaneous forward Pell order')
   need((B-A)%U==0 and (S-X)%U==0 and (R-k)%(4*Y)==0 and (B-1)%(4*Y)==0,'simultaneous Pell congruences')
   counters['joint_Pell_orientation_cases']+=1
 return dict(counters)

def sparse_check(folder):
 e=json.loads((folder/'equation.json').read_text());q=json.loads((folder/'expanded_polynomial.json').read_text());p=collections.defaultdict(int)
 for r in e['residuals']:
  for a,m in r['terms']:
   need(len(m)<=2 and all(0<=j<len(e['variables']) for j in m),'quadratic residual bounds')
   for b,n in r['terms']:p[tuple(sorted(m+n))]+=a*b
 expected=[[c,list(m)] for m,c in sorted(p.items()) if c]
 need(expected==q['terms'],'independent SOS expansion mismatch')
 need(max(len(m) for c,m in expected)==4,'quartic degree')
 return {'variables':len(e['variables']),'residuals':len(e['residuals']),'monomials':len(expected),'sha256':hashlib.sha256((folder/'expanded_polynomial.json').read_bytes()).hexdigest()}

def height_certificate():
 spec=importlib.util.spec_from_file_location('self_authored_architecture',ROOT/'build_architecture_final.py');b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 result={}
 for mode in ['ordinary','group_majorant']:
  c=b.Circuit();env={name:c.v(name) for name in ['t','x','y','m','M0','p','q','v','a','b','c','d','S','Sp','u','vq','r','rp']};idx=c.v('index')
  ep,fp=c.source(env,idx,True,mode=mode);known={};records=[]
  def h(a):return (0 if a[1]<=1 else 1) if a[0]=='c' else known.get(a[1],1)
  for (op,a,d),v in c.cache.items():
   hv=max(h(a),h(d))+1 if op=='add' else h(a)+h(d)
   known[v[1]]=hv;records.append({'op':op,'left':a,'right':d,'output':v,'height':hv})
  D=max(h(ep),h(fp))+1;rounded=1<<(D-1).bit_length()
  need(rounded==8388608,'unexpected fixed majorant exponent')
  result[mode]={'natural_input_height':1,'radius_floor':4,'nodes':records,'roots':[ep,fp],'raw_exponent':D,'rounded_exponent':rounded,'squarings':23}
 return result

def replay():
 cases=[('rounded_positive','build_architecture_final.py',['--coarse-majorant']),('rounded_negative','build_architecture_final.py',['--coarse-majorant','--negative-moduli']),('factorial_carrier','build_architecture_final.py',['--coarse-majorant','--factorial-carrier'])]
 with tempfile.TemporaryDirectory(prefix='architecture-replay-') as t:
  for folder,script,flags in cases:
   output=pathlib.Path(t)/folder
   subprocess.run([sys.executable,str(ROOT/script),'--oriented-power',*flags,'--output',str(output)],check=True,stdout=subprocess.DEVNULL)
   for file in ['equation.json','expanded_polynomial.json','affine_restoration.json','circuit.json','BUILD.json']:
    need((output/file).read_bytes()==(ROOT/folder/file).read_bytes(),'clean replay mismatch '+folder+'/'+file)
 return len(cases)

def main():
 p=argparse.ArgumentParser();p.add_argument('--no-rebuild',action='store_true');args=p.parse_args()
 out={'arithmetic_fixtures':arithmetic_fixtures(),'scope':'finite fidelity checks, not an all-input or kernel proof'}
 hc=height_certificate();(ROOT/'HEIGHT_CERTIFICATE.json').write_text(json.dumps(hc,separators=(',',':'),sort_keys=True)+'\n')
 out['height_summary']={k:{f:v[f] for f in ['raw_exponent','rounded_exponent','squarings']} for k,v in hc.items()}
 out['sparse_checks']={n:sparse_check(ROOT/n) for n in ['rounded_positive','rounded_negative','factorial_carrier']}
 if not args.no_rebuild:out['clean_replayed_variants']=replay()
 (ROOT/'CHECKS.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
