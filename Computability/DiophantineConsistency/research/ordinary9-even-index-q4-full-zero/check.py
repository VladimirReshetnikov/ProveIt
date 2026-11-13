from pathlib import Path
from hashlib import sha256
import json,sys,resource
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
resource.setrlimit(resource.RLIMIT_AS,(192*1024**2,192*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
D=Path('research/ordinary9-even-index-q4-full-zero')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
G9=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
G10=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text())
assert len(G9['source'])==64 and len(G10['source'])==61
assert G9['fixed_numerals']==G10['fixed_numerals']==['beta','K0','MC','MF']
assert G9['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_r','n_eta','n_zeta','n_gamma']
assert G10['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
q=4;beta=3;K0=MC=MF=1;L=6;n=78;m=84
assert n==L*(2*L+1) and m==n+L and m%2==0
X=2**m;Y=2**L;U=Y*q*q;M=X*Y*Y;a=Y*(X+1);H=4*a+3
assert X%q==0 and Y==q**3 and H%2==1

def pell(A,j):
 x,y=1,0;delta=A*A-1
 for _ in range(j):x,y=A*x+delta*y,x+A*y
 return x,y
tau,yFirst=pell(2*M+1,n);k=2*yFirst;g,c=pell(a+2,m)
assert tau*tau==1+M*(M+1)*k*k
assert g*g==1+((a+2)**2-1)*c*c
eta=c-Y*k;assert 0<=eta<k
R=155;assert R==2*n-1 and k>R+1 and (k-R-1)%U==0
B=2*(X+1)-1;assert B>0 and B%beta==0
h=B//beta
numer=g-X-a*c;assert numer>0 and numer%H==0
gamma=numer//H+(k-R-1)//U
ell=M*k
r=tau-ell-k+(k*beta+1)*h
assert min(h,gamma,r,eta,k-eta-1)>=0
ports={'beta':beta,'K0':K0,'MC':MC,'MF':MF}
common={'n_J':1,'n_F':0,'n_alpha':0,'n_w':X//q,'n_s':0,
        'n_eta':eta,'n_zeta':k-eta-1,'n_gamma':gamma}
v9=ports|common|{'n_r':r}
v10=ports|common|{'n_h':h,'n_tau':tau}
def evaluate(graph,vals):
 vals=vals.copy()
 for name,op,left,right in graph['source']:
  assert name not in vals
  left=left if isinstance(left,int) else vals[left];right=right if isinstance(right,int) else vals[right]
  vals[name]=left+right if op=='+' else left-right if op=='-' else left*right
 return vals
a9=evaluate(G9,v9);a10=evaluate(G10,v10)
for aout in [a9,a10]:
 for key,val in {'q':q,'X':X,'Y':Y,'U':U,'a':a,'H':H,'R':R,'k':k,'c':c,'ell':ell,'Dstar':U*g,'A1':0,'out':0}.items():assert aout[key]==val,key
assert a9['Z']==beta*tau and a9['A0']==0
assert a10['Bres']==a10['firstres']==0
# The 64-row graph contains the main ordinate y_m for even m explicitly.
assert c==pell(a+2,m)[1] and m>0 and m%2==0
for vals in (v9,v10):assert all(isinstance(x,int) and x>=0 for x in vals.values())
max_bits=max(x.bit_length() for vals in (v9,v10) for x in vals.values());assert max_bits<8000
# Hash bytes without decimal conversion; signs handled explicitly.
def digest(x):
 assert x>=0
 return sha256(x.to_bytes(max(1,(x.bit_length()+7)//8),'big')).hexdigest()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'noncompact_ports':ports,'first_pell_index':n,'main_pell_index':m,'main_index_even':True,
 'rows_evaluated_9_graph':len(G9['source']),'rows_evaluated_10_graph':len(G10['source']),
 'both_literal_outputs_zero':True,'natural_witnesses_verified':True,
 'r_bits':r.bit_length(),'eta_bits':eta.bit_length(),'gamma_bits':gamma.bit_length(),'max_input_bits':max_bits,
 'main_c_sha256':digest(c),'first_tau_sha256':digest(tau),'main_root_sha256':digest(g),
 'fixed_compact_tuple':False,'original_parent_other_witness_excluded':False,
 'lean_executed':False},sort_keys=True,indent=2))
