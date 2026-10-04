"""Independent inert-array review of the two-program U21 sharing successor."""
import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'residue_affine_sparse_shared476.py':'52e09d2b3474e37c6116e16b7a1ee59395a337a5ff381b4881ae616ecbaafddf',
 'residue_affine_sparse_shared476.json':'90e6e265ae1eb9a1cd1239255c14da3d3c6e5841f330f7a6220536d182778ba8',
 'residue_affine_sparse_shared476.md':'cbd4d632b813f0ad34a9e5b35894d187ca229c14f1d4cf3af269a518ab57fcd4',
}
AUTHOR_PINS={
 'residue_affine_sparse_shared470.py':'6705f2abfc330427f47aaf8ee3cbad25ca311e86014e0499c994fdf90b97a586',
 'residue_affine_sparse_shared470.json':'2f7715aa5449118cfad292595bc7cde374587723a123b3c69a0d180cb51993e4',
 'residue_affine_sparse_shared470.md':'b50e62d1eedef24ef390562c70cca69bbbb4b2dd5d6c7f1134ed99b4fb278570',
}
PAIRS={
 'prime_selector_99':('edge_16','control_codes__target_class_35','prime_selector_98'),
 'prime_selector_101':('prime_selector_99','control_codes__duplicate_state_3','prime_selector_100'),
 'prime_selector_105':('prime_selector_103','control_codes__duplicate_state_2','prime_selector_104'),
 'prime_selector_107':('prime_selector_105','control_codes__duplicate_state_5','prime_selector_106'),
 'prime_selector_109':('prime_selector_107','control_codes__duplicate_state_8','prime_selector_108'),
 'control_codes__current_positive_19':('u21_grouped_J_0','prime_selector_95','control_codes__current_multiple_9'),
}
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def serial(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(path):
 def pairs(ps):
  d={}
  for k,v in ps:require(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  require(type(r)is list and len(r)==4,'row shape')
  n,op,a,b=r
  require(type(n)is str and n not in d and op in ('+','-','*'),'SSA definition')
  require(all(type(v)in(int,str)for v in(a,b)),'operand type');d[n]=r
 return d

def audit(rows,ports):
 d=table(rows);known=set(ports)
 for n,o,a,b in rows:
  require(n not in known and all(type(v)is int or v in known for v in(a,b)),'source order')
  known.add(n)
 reached=set();todo=['norm_output']
 while todo:
  v=todo.pop()
  if type(v)is str and v not in reached:
   reached.add(v)
   if v in d:todo.extend(d[v][2:])
 require(known==reached,'all rows and ports live')
 c=Counter(r[1]for r in rows)
 return [len(rows),c['*'],c['+']+c['-']]

def expected_graph(old,new):
 d={n:r[:]for n,r in table(old).items()};users={}
 for target,(a,b,dead)in PAIRS.items():
  users[dead]=[r[0]for r in old if dead in r[2:]]
  require(users[dead]==[target],'private deletion')
  d[target]=[target,'+',a,b];del d[dead]
 require(d==table(new),'complete independently reconstructed definitions')
 # Independent Kahn traversal checks simultaneous edits, not only old/new order.
 indeg={n:len({v for v in r[2:]if type(v)is str and v in d})for n,r in d.items()}
 follow={n:[]for n in d}
 for n,r in d.items():
  for v in set(r[2:]):
   if type(v)is str and v in follow:follow[v].append(n)
 q=deque(n for n in d if indeg[n]==0);visited=[]
 while q:
  n=q.popleft();visited.append(n)
  for k in follow[n]:
   indeg[k]-=1
   if indeg[k]==0:q.append(k)
 require(len(visited)==len(d),'simultaneous graph cyclic')
 return users

def symbolic(old,new,ports):
 # Automatically normalize every affine cone in the literal supplied hats.
 # No author-designated cut or author coefficient vector is accepted.
 pool={};zero=(0,)*37
 def atom(t):
  if t not in pool:pool[t]=len(pool)
  return ('atom',pool[t])
 def const(c):return ('affine',zero[:36]+(c,))
 def calc(op,a,b):
  if a[0]==b[0]=='affine':
   x,y=a[1],b[1]
   if op!='*':return ('affine',tuple(u+(v if op=='+'else-v)for u,v in zip(x,y)))
   if not any(x[:36]):return ('affine',tuple(x[36]*v for v in y))
   if not any(y[:36]):return ('affine',tuple(y[36]*u for u in x))
  return atom((op,a,b))
 seed={n:atom(('port',n))for n in ports}
 for i in range(36):seed[f'edge{i}_hat']=('affine',tuple(int(j==i)for j in range(37)))
 envs=[]
 for rows in(old,new):
  e=seed.copy()
  for n,op,a,b in rows:
   a=const(a)if type(a)is int else e[a];b=const(b)if type(b)is int else e[b]
   e[n]=calc(op,a,b)
  envs.append(e)
 require(all(envs[0][n]==value for n,value in envs[1].items()),'all retained values/output exact identity')
 return {n:list(envs[1][n][1])for n in PAIRS}

def degree(rows,ports):
 d=table(rows);cuts=['native__wn2','native__R12','native__R10a','native__gam','native__a4m5'];z=(0,)*5
 memo={n:{tuple(int(i==j)for i in range(5)):1}for j,n in enumerate(cuts)}
 def expand(v):
  if type(v)is int:return {z:v}if v else{}
  if v in memo:return memo[v]
  _,op,a,b=d[v];p,q=expand(a),expand(b);s={}
  if op=='*':
   for m,c in p.items():
    for k,e in q.items():
     u=tuple(x+y for x,y in zip(m,k));s[u]=s.get(u,0)+c*e
  else:
   s=p.copy()
   for k,e in q.items():s[k]=s.get(k,0)+(e if op=='+'else-e)
  memo[v]={k:c for k,c in s.items()if c};return memo[v]
 norm=expand('native__R15');require(len(norm)==6,'literal six-term cancellation')
 expected={ (2,0,0,0,0):1,(1,1,1,0,0):2,(1,0,0,1,0):2,
            (0,1,1,1,0):2,(0,0,0,2,0):1,(0,0,2,0,1):-1 }
 require(norm==expected,'literal norm coefficients')
 high={n:1 for n in ports};naive=high.copy();weights=[];term=[]
 for n,op,a,b in rows:
  for e in(high,naive):
   x,y=(0 if type(v)is int else e[v]for v in(a,b));e[n]=x+y if op=='*'else max(x,y)
  if n=='native__R15':
   weights=[high[n]for n in cuts];term=[sum(a*b for a,b in zip(k,weights))for k in norm];high[n]=max(term)
 factors=['native__'+n for n in ['R15','P17','first_unit','bs_q','f_square_minus_one','index_unit','linear_unit']]+['sparse_repunit_unit']
 fv=[high[n]for n in factors]
 require(weights==[312,379,68,380,379],'two-program degree weights')
 require(fv==[827,1926,448,66,1032,380,380,3],'all factor bounds')
 require(high['norm_output']==5160 and naive['norm_output']==5227,'degree upper propagation')
 return dict(cuts=cuts,weights=weights,norm_coefficients=[[list(k),v]for k,v in sorted(norm.items())],term_bounds=sorted(term),factor_bounds=fv,uniform_upper=5160,naive_upper=5227,exact_degree_claimed=False)

def build(root,author):
 for base,pins in[(root,PINS),(author,AUTHOR_PINS)]:
  for n,h in pins.items():require(sha((base/n).read_bytes())==h,'file pin '+n)
 require(len(AUTHOR_PINS)==3,'author freeze pins not set')
 parent=read(root/'residue_affine_sparse_shared476.json');child=read(author/'residue_affine_sparse_shared470.json')
 require(parent['source_sha256']==PINS['residue_affine_sparse_shared476.py'],'parent helper binding')
 require(child['source_sha256']==AUTHOR_PINS['residue_affine_sparse_shared470.py'],'author helper binding')
 for n,h in child['dependencies'].items():require(sha((root/n).read_bytes())==h,'author dependency '+n)
 p,c=parent['packet'],child['packet'];before=serial(parent);old,new=p['source'],c['source']
 require(p['source_sha256']==sha(serial(old))and c['source_sha256']==sha(serial(new)),'array hashes')
 for key in ['parameters','fixed_program_parameters','witnesses','output','valid_recipe','polynomial_degree_upper_bound','exact_degree_claimed']:
  require(c[key]==p[key],'interface '+key)
 ports=p['parameters']+p['witnesses'];require(p['parameters']==['program','radix_program','input']and len(ports)==70 and len(p['witnesses'])==67,'two-program interface')
 require(audit(old,ports)==[476,176,300]and audit(new,ports)==[470,175,295],'complete ledgers')
 require(c['ledger']==dict(operations=470,multiplications=175,additions_subtractions=295,witnesses=67),'reported full ledger')
 require(c['certificate_ledger']==dict(operations=450,multiplications=168,additions_subtractions=282,equations=7,witnesses=67),'reported certificate ledger')
 require(c['valid_recipe']=='C is a positive dyadic integer, C>=64 and C>program; default control plan only.','valid fixed recipe')
 users=expected_graph(old,new);affine=symbolic(old,new,ports);deg=degree(new,ports)
 d=table(new);native=[r for r in old if r[0].startswith('native__')];final=old[-20:]
 require(len(native)==72 and all(d[r[0]]==r for r in native),'literal entire native')
 require(final[-1][0]=='norm_output'and all(d[r[0]]==r for r in final),'literal whole finalizer')
 require(d['height_85']==['height_85','+','input','height_slack']and d['radix_86']==['radix_86','*','radix_program','height_85']and 'height_83'not in d,'actual C recipe')
 fc=Counter(r[1]for r in final);require([len(new)-20,175-fc['*'],295-fc['+']-fc['-']]==[450,168,282],'certificate ledger')
 require(serial(parent)==before,'parent packet immutable')
 return dict(status='PASS_INDEPENDENT_U21_SHARED470',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,author_pins=AUTHOR_PINS,
  checked_rows=470,retained_expression_identities=470,ports=70,witnesses=67,complete_ledger=[470,175,295],certificate_ledger=[450,168,282],
  affine_hat_coefficients=affine,private_deleted_users=users,native_rows_literal=72,finalizer_rows_literal=20,degree=deg,
  scope='Direct whole-polynomial identity to actual two-program476 on identical supplied coordinates; E=3^e and fixed dyadic C>=64,C>E; no predecessor execution, no cross-recipe projection or history materialization')
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=ROOT);a.add_argument('--author-root',type=Path,default=Path('/tmp'));g=a.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);v=a.parse_args();r=build(v.root,v.author_root)
 if v.output:
  with v.output.open('x')as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:require(serial(r)==serial(read(v.expect)),'exact review receipt')
 print(r['status'],r['complete_ledger'],'degree <=',r['degree']['uniform_upper'])
if __name__=='__main__':main()
