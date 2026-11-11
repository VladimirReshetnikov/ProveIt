from pathlib import Path
import hashlib,json,math,subprocess,sys
root=Path(__file__).resolve().parents[2]; d=root/'research/current14-trace-current-port-obstruction'
pins={'README.md':'480d117b408ed03363a823be06bb3d263ad3d53ef76a38ca76c55c1fc04861fe','check.py':'a7e49a447faf15445b09a4d27444c341af38af1be33b34074d48d8b2939ad924','result.json':'a3449c4f688cef5804aa42e8ea3e9d890141053129342374cd70a9943f0be353'}
for n,h in pins.items(): assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
observed=subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')]); assert observed==(d/'result.json').read_bytes()
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-trace-congruence-obstruction-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
# Separate full-integer check of two small instances; no big numbers printed.
instances=[]
for B,p in [(3,12289),(3,18433)]:
 q=1<<B; assert all(p%i for i in range(2,math.isqrt(p)+1)); D=4*q**3*(q+1)//3;assert (p-1)%D==0 and p%8==1
 h=(p-1)//D; Y=q**3*h; X=q; H=4*Y*(X+1)+3;assert H==3*p
 order=1;v=2%p
 while v!=1: v=2*v%p;order+=1
 k=math.lcm(2,order);R=B+k
 assert k<=(p-1)//2 and k%2==0 and R%2==1 and R+1<X*Y and pow(2,R,H)==X and X!=2**R
 a=Y*(X+1);u,v=0,1
 for _ in range(R):u,v=v,2*(a+2)*v-u
 numerator=3*X*u-2*(X*X-1);gamma,rem=divmod(numerator,H);assert rem==0 and gamma>0
 instances.append({'B':B,'prime':p,'R':R,'positive_integral_gamma':True})
print(json.dumps({'status':'PASS_EXTERNAL_MATHEMATICAL_REVIEW','toy_full_integer_instances':instances,'scope':'Actual beta symbolic local existence via Dirichlet; no rank, Pell norms, full zero, Lean or PDF'},indent=2))
