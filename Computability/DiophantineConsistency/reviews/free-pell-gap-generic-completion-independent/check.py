from pathlib import Path
import hashlib,json,subprocess,sys,math
root=Path(__file__).resolve().parents[2];d=root/'research/free-pell-gap-generic-completion'
pins={'README.md':'14201bdce6293c730d62745fae0bb5b92f3c64199fc5c4be87dc51768f212e89','check.py':'715705a2e198adaa8c6feb6da387d72946c3e0c183de48a3644e066016d7acdf','result.json':'a037ffcf0b8efc9ce7f5bbfad9dfe1000854efc035d367bff775f5902da46c5f'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());rs={x[0]:x[1:] for x in g['source']};assert rs['normalized_S']==['*','i','Dc2'] and rs['scaled_Ns']==['-','scaled_f2','normalized_S2'] and rs['V']==['-','f2inner','c']
controls=[]
for A,r,R in [(3,2,5),(4,3,3),(5,2,7)]:
 delta=A*A-1;D,c=1,0
 for _ in range(r):D,c=A*D+delta*c,D+A*c
 f,L=1,0
 for _ in range(2*c):f,L=D*f+delta*c*L,c*f+D*L
 assert c>=2 and L%(c*c)==0 and f*f-delta*L*L==1 and math.gcd(A,f)==1
 S=delta*L;M=S*S-1;mods=[M,c,f*f];assert all(math.gcd(mods[i],mods[j])==1 for i in range(3) for j in range(i));period=math.prod(mods);V=sum((z%m)*(period//m)*pow(period//m,-1,m) for z,m in zip([1,-R,-c],mods))%period+period
 for _ in range(20):
  t,rem=divmod(V*V-1,M);assert rem==0 and t>0;T,rem=divmod(V+c+f*f*R,c*f*f);assert rem==0 and T>0 and V==f*f*(c*T-R)-c and V*V-M*t==1
  if math.isqrt(V*V+t)**2!=V*V+t:break
  V+=period
 else:raise AssertionError('finite control had no nonsquare')
 controls.append({'A':A,'main_index':r,'nonsquare':True})
print(json.dumps({'status':'PASS_EXTERNAL_MATHEMATICAL_REVIEW','independent_small_controls':controls,'scope':'Conditional strong/aux completion only; no actual-port seed or coherent Lean proof'},indent=2))
