#!/usr/bin/env python3
"""Independent binary Pell reconstruction and exact full graph evaluation."""
import hashlib,json,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(192*1024**2,192*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
nine=json.loads((root/'research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
ten=json.loads((root/'research/ordinary10-two-norm-divisible61/candidate.json').read_text())
parent=json.loads((root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
assert len(nine['source'])==64 and len(ten['source'])==61
assert nine['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_r','n_eta','n_zeta','n_gamma']
assert ten['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
ports=[3,1,1,1]
assert all(g['fixed_numerals']==['beta','K0','MC','MF'] for g in (nine,ten,parent))
# Compare exact shared ordered expressions, not just values at the witness.
def trees(g):
 e={n:('input',n) for n in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:
  a=e[a] if isinstance(a,str) else ('lit',a);b=e[b] if isinstance(b,str) else ('lit',b)
  e[name]=(op,a,b)
 return e
nt,pt=trees(nine),trees(parent)
for field in ('A0','A1','R','c','a','Dstar'):assert nt[field]==pt[field],field
# Binary Pell powers (different from the author's iteration).
def pell(A,n):
 D=A*A-1
 def mul(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
 z=(1,0);v=(A,1)
 while n:
  if n&1:z=mul(z,v)
  v=mul(v,v);n//=2
 return z
q=4;X=1<<84;Y=1<<6;U=Y*q*q;M=X*Y*Y;a=Y*(X+1);H=4*a+3
n=78;m=84;tau,yf=pell(2*M+1,n);k=2*yf;g,c=pell(a+2,m)
assert tau*tau==1+M*(M+1)*k*k and g*g==1+((a+2)**2-1)*c*c
assert Y*k<=c<(Y+1)*k and m>0 and m%2==0
B=2*(X+1)-1;assert B%3==0;h=B//3
p=g-X-a*c;z=k-155-1
assert p%H==0 and z%U==0
assert p//H>=0 and z//U>=0
gamma=p//H+z//U
eta=c-Y*k;zeta=k-eta-1;ell=M*k
rr=tau-ell-k+(3*k+1)*h
vals9=[1,0,0,X//q,0,rr,eta,zeta,gamma]
vals10=[1,0,0,X//q,0,h,tau,eta,zeta,gamma]
assert X%q==0 and 0<=eta<k and all(v>=0 for v in vals9+vals10)
def evalgraph(graph,values):
 e=dict(zip(graph['witnesses'],values));e.update(zip(graph['fixed_numerals'],ports))
 for name,op,a,b in graph['source']:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
x=evalgraph(nine,vals9);y=evalgraph(ten,vals10)
for e in (x,y):
 assert e['R']==155 and e['c']==c and e['Dstar']==U*g and e['A1']==0 and e['out']==0
assert x['Z']==3*tau and x['A0']==0
assert y['Bres']==0 and y['firstres']==0
print(json.dumps({'ports':ports,'first_index':n,'main_index':m,'main_index_even':True,
 'first_and_main_Pell_norms_exact':True,'all_three_divisions_exact':True,
 'all_inputs_natural':True,'shared_parent_norm_trees_exact':True,
 'literal_nine_graph_rows_evaluated':64,'literal_ten_graph_rows_evaluated':61,
 'both_graph_outputs_zero':True,'largest_witness_bits':max(v.bit_length() for v in vals9+vals10),
 'same_data_parent_completion_excluded_by_reviewed_theorem':True,
 'other_parent_witnesses_or_compact_port_excluded':False,'lean_executed':False},indent=2,sort_keys=True))
