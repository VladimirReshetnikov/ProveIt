from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-carrier60-inverse-boundary')
for p,h in json.loads((D/'pins.json').read_text()).items(): assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text());g=json.loads((D/'candidate.json').read_text())
expected=[]
for row in p['source']:
 n=row[0]
 if n=='alpha':expected.append(['C','+','n_C',1]);continue
 if n=='C' or n=='g44':continue
 if n=='G':expected.extend([['qqF','*','q','qF'],['G','-','qqF','C']]);continue
 expected.append(row)
assert g['source']==expected and g['witnesses']==[('n_C' if n=='n_alpha' else n) for n in p['witnesses']]
assert len(g['source'])==60 and len(g['witnesses'])==10
# Fresh topological/liveness traversal.
d={};leaves=set(g['witnesses']+g['fixed_numerals'])
for name,op,a,b in g['source']:
 assert name not in d and name not in leaves and op in '+-*'
 assert isinstance(a,int) or a in leaves or a in d
 assert isinstance(b,int) or b in leaves or b in d
 d[name]=(op,a,b)
live=set();used=set()
def walk(x):
 if isinstance(x,int):return
 if x not in d:used.add(x);return
 if x in live:return
 live.add(x);_,a,b=d[x];walk(a);walk(b)
walk('out');assert len(live)==60 and used==leaves
# Construct Pell witnesses exactly, only a few hundred digits.
q=2;w=17;s=2;X=q*w;Y=q**3*s;M=X*Y*Y;A=Y*(X+1)+2;H=4*Y*(X+1)+3
assert (X,Y,M,A,H)==(34,16,8704,562,2243)
tau,k=1,0
for _ in range(45): tau,k=(2*M+1)*tau+2*M*(M+1)*k,2*tau+(2*M+1)*k
gx,c=1,0
for _ in range(67):gx,c=A*gx+(A*A-1)*c,gx+A*c
eta=c-Y*k
assert 0<=eta<k and tau*tau==1+M*(M+1)*k*k and gx*gx==1+(A*A-1)*c*c
num=gx-X-(A-2)*c
assert num>0 and num%H==0 and pow(2,67,H)==X%H
t=num//H;U=Y*q*q;R=k-1+U*t
ports={'beta':1,'K0':1,'MC':R-3,'MF':0}
witness={'n_J':1,'n_F':0,'n_C':0,'n_w':w,'n_s':s-1,'n_h':X,'n_tau':tau,'n_eta':eta,'n_zeta':k-eta-1,'n_gamma':0}
assert all(v>=0 for v in ports.values()) and all(v>=0 for v in witness.values())
values=ports|witness
for n,op,a,b in g['source']:
 a=a if isinstance(a,int) else values[a]; b=b if isinstance(b,int) else values[b]
 values[n]=a+b if op=='+' else a-b if op=='-' else a*b
assert values['q']==q and values['X']==X and values['Y']==Y and values['C']==1
assert values['R']==R and values['k']==k and values['c']==c and values['Dstar']==U*gx
assert values['Bres']==values['firstres']==values['A1']==values['out']==0
# The direct inverse would set old alpha = q-F-C, which is zero.
assert values['qF']-values['C']==0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'candidate_live_operations':len(live),'candidate_live_inputs':len(used)-len(g['fixed_numerals']),'first_pell_index':45,'main_pell_index':67,'all_natural_witnesses_and_positive_beta_K0':True,'literal_candidate_output_zero':True,'reconstructed_old_alpha':0,'ports_are_compact':False,'existential_nonequivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
