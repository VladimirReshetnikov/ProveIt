from pathlib import Path
import hashlib,json,subprocess,sys,math
root=Path(__file__).resolve().parents[2];d=root/'research/current14-carrier64-free-en-toy-zero'
pins={'README.md':'78b909e3b31b92785c9e886bac2d41ebd6f83a7aaad875d59f581968e45e9874','check.py':'21bbfc32f4983b3da819f86c69a2d399744128a1f2dc46e7b8956f279d2c9ec9','result.json':'77439ce04d6fb5de703f48cdd8568b821118633063dfaf6214ade7e817dbc06c'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
g=json.loads((root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json').read_text());rs={r[0]:r[1:] for r in g['source']}
expected={'ell':['*','E','kY'],'kY':['*','k','Y'],'tau_partial':['+','En','k'],'tau':['-','tau_partial','R'],'N0':['-','tau2','first_product'],'Nt':['-','transport_partial','zqm'],'N1':['-','main_square','Dc2'],'polynomial':['-','product4','Delta']}
for n,r in expected.items():assert rs[n]==r
q=32;beta=31;K=29;MC=30;MF=33;F=30;alpha=1;J=1;C=q-F-alpha;gap=beta*(q-F)+alpha;R=gap*(q*q-1)+(MC+q*MF)*J;h=65280;t=256
assert C==1 and gap==63 and R==65535 and R%4==3 and h>1
# Compare exact powers by exponents, and strict bounds used for Pell ratio.
r=R-1;s=h-1;assert r*(R+t+1)-1-s*(R+2*t+2)==t
assert r*(2*(1<<t)+3)*(1<<t)>2*s and 2*s < (1<<(R+2*t))
assert 4*(1<<t)*r < (1<<R)
assert (R-2*h+1)==-65024 and 1<<(R+t)>65024
assert pow(2,R-5,beta)==1 and (K+2)%beta==0
# Exact independent small Pell-ring completion check for the same odd-index formula.
A=3;N=3;delta=A*A-1;D=4*A**3-3*A;c=4*A*A-1;f,L=1,0
for _ in range(70):f,L=D*f+delta*c*L,c*f+D*L
assert f*f-delta*L*L==1 and L%(c*c)==0
S=delta*L;y=4*S*S-1;V=4*S*S-3
assert (V+c)%(f*f)==0 and (V+N)%c==0 and V*V*S*S-(S*S-1)*y*y==1
T,rem=divmod(V+c+f*f*N,c*f*f);assert rem==0 and T>0 and V==f*f*(c*T-N)-c
print(json.dumps({'status':'PASS_SYMBOLIC_EXTERNAL_REVIEW','toy_ports':[31,29,30,33],'graph_gates':64,'actual_pell_witness_expanded':False,'scope':'toy-port symbolic zero and same-other-coordinate obstruction only; no current-port, Lean or unrestricted nonequivalence'},indent=2))
