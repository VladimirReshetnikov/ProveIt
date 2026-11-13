from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-carrier60-positive-j-alpha-zero-mask-counterexample')
for p,h in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary10-carrier60-inverse-boundary/candidate.json').read_text())
assert g['domain']=='nonnegative integers'
assert g['fixed_numerals']==['beta','K0','MC','MF']
assert g['witnesses']==['n_J','n_F','n_C','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
assert len(g['source'])==60
beta=1;q=2;X=2;Y=8;U=32;M=128;a=24;H=99;A=26;delta=675
assert H==4*a+3 and A==a+2 and delta==A*A-1
# Entire Pell witnesses, not modular proxies.
tau,k=1,0
for _ in range(8659):tau,k=(2*M+1)*tau+2*M*(M+1)*k,2*tau+(2*M+1)*k
groot,c=1,0
for _ in range(13681):groot,c=A*groot+delta*c,groot+A*c
assert tau*tau==1+M*(M+1)*k*k
assert groot*groot==1+delta*c*c
eta=c-Y*k; zeta=k-eta-1
assert eta>=0 and zeta>=0
num=U*(groot-X-a*c)
assert num%H==0
shift=num//H
R=5
numgamma=shift-R-1+k
assert numgamma>=0 and numgamma%U==0
gamma=numgamma//U
# Evaluate the exact graph over Z[K0]; K0 need not be materialized.
def norm(a):
    while a and a[-1]==0:a.pop()
    return a
def const(x):return [] if x==0 else [x]
def add(a,b):return norm([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def neg(a):return [-x for x in a]
def mul(a,b):
    if not a or not b:return []
    d=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):d[i+j]+=x*y
    return norm(d)
K=[0,1]
v={'beta':const(1),'K0':K,'MC':[],'MF':const(1),
   'n_J':const(1),'n_F':[],'n_C':const(0),'n_w':const(1),'n_s':[],
   'n_h':[1,1],'n_tau':const(tau),'n_eta':const(eta),
   'n_zeta':const(zeta),'n_gamma':const(gamma)}
def at(x):return const(x) if isinstance(x,int) else v[x]
for name,op,x,y in g['source']:
    assert name not in v and op in '+-*'
    x,y=at(x),at(y)
    v[name]=add(x,y) if op=='+' else add(x,neg(y)) if op=='-' else mul(x,y)
for name,val in {'q':q,'X':X,'Y':Y,'U':U,'C':1,'F':1,'k':k,'c':c,
                 'a':a,'H':H,'Delta':delta,'R':R,'Dstar':U*groot,
                 'Bres':0,'firstres':0,'A1':0,'out':0}.items():
    assert v[name]==const(val),name
assert add(v['qF'],neg(v['C']))==const(0)
assert beta>0 and 0<=0<beta and 0<=1<2*beta
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'ports':'beta=1, K0 arbitrary natural, MC=0, MF=1',
 'first_pell_index':8659,'main_pell_index':13681,
 'positive_J':True,'mask_bounds_hold':True,'all_inputs_natural':True,
 'symbolic_K0_literal_output_zero':True,'reconstructed_old_alpha':0,
 'actual_compact_beta_tested':False,'61_graph_nonequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
