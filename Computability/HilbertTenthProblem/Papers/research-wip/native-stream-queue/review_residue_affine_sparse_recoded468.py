"""Independent full-source/control-domain audit; all author/parent files inert."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
AUTHOR_PINS={
 'residue_affine_sparse_recoded468.py':'4b73c18e91473205dfb50edaf3e289898af305b14781ca1e10ce8a2ec06d834f',
 'residue_affine_sparse_recoded468.json':'1aa26a73ebce4e5a8cfeb443b7d2aa296bbf7816a5c842728f6a3862872936b4',
 'residue_affine_sparse_recoded468.md':'93607b73b03769c46ec698c2b2d1bac83e3c192e81c9d29d4d000de66ef35ea7',
}
PINS={'residue_affine_sparse_shared471.py':'8940d9c5b008bbe9d6ea210d938634afec1e59a76362b2c3a4aa25c53d460246','residue_affine_sparse_shared471.json':'4732844a06fb9285d9fc57aa8dcd220e3664f965ec850393c830d2a453832ced','residue_affine_sparse_shared471.md':'12c4725b79fe4e9173bef944100e41612b20e213f13b8f470d34802d6c5839c4','residue_affine_sparse_factored.json':'39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda','residue_affine_sparse_control_codes.json':'2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d'}
OLD_CODES=[0,1,14,21,9,17,13,10,5,18,8,25,41,32,57,3,12,4,24,2,6,7,63]
NEW_CODES=[0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14]
OUTPUT='norm_output'
def require(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def serial(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def load(p):
 def pairs(xs):
  d={}
  for k,v in xs:require(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  require(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  require(type(n)is str and n not in d and o in ('+','-','*'),'SSA binary producer')
  require(all(type(v)in(int,str)for v in(a,b)),'operand type');d[n]=r
 return d
def closure(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in d:todo.extend(d[n][2:])
 return seen

def audit(rows,ports):
 d=table(rows);seen=set(ports);counts=Counter()
 for n,o,a,b in rows:
  require(n not in seen and all(type(v)is int or v in seen for v in(a,b)),'topological source')
  seen.add(n);counts[o]+=1
 require(closure(d,[OUTPUT])==seen,'complete port/row liveness')
 return [len(rows),counts['*'],counts['+']+counts['-']]

def add(a,b,sign=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+sign*c
 return {m:c for m,c in d.items()if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for k,e in b.items():
   q=tuple(sorted(m+k));d[q]=d.get(q,0)+c*e
 return {m:c for m,c in d.items()if c}
def expand(rows,root,cuts):
 d=table(rows);memo={n:{(n,):1}for n in cuts}
 def run(n):
  if type(n)is int:return {():n}if n else{}
  if n in memo:return memo[n]
  require(n in d,'closed polynomial cone '+n);_,o,a,b=d[n];a,b=run(a),run(b)
  memo[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1);return memo[n]
 return run(root)
def record(p):return [[list(k),v]for k,v in sorted(p.items())]

def reconstruct_edges(program,primes):
 out=[[0,0,'I',2,1,2,1,2],[0,1,'I',2,1,2,1,2]]
 for q,row in enumerate(program,1):
  op,reg=row[:2];p=primes[reg];go=[a+1 for a in row[2:]]
  if op=='I':
   require(len(go)==1,'increment arity');out.append([q,go[0],op,p,1,p,1,p])
  else:
   require(op in('D','T')and len(go)==2,'branch arity')
   out.append([q,go[0],op,p,p,1,p,1]if op=='D'else[q,go[0],op,p,p,p,p,p])
   out.append([q,go[1],'Z',p,p,p,1,1])
 return out

def controls(old,new,edges,info):
 hats={f'edge{i}_hat'for i in range(36)};raw={f'edge_{i}'for i in range(36)}
 roots=[('control_codes__current_positive_29','control_codes__target_difference_70'),(info['current'],info['following'])]
 all_words=[]
 for rows,codes,names in[(old,OLD_CODES,roots[0]),(new,NEW_CODES,roots[1])]:
  for end,root in enumerate(names):
   weights=[codes[e[end]]for e in edges];p=expand(rows,root,hats)
   expected={(f'edge{i}_hat',):v for i,v in enumerate(weights)if v};expected[()]=-sum(weights)
   require(p==expected,'actual hat coefficients '+root);all_words.append(dict(root=root,coefficients=record(p)))
 dc=add(expand(new,roots[1][0],raw),expand(old,roots[0][0],raw),-1)
 dn=add(expand(new,roots[1][1],raw),expand(old,roots[0][1],raw),-1)
 require(dc=={('edge_4',):1,('edge_11',):1,('edge_12',):1,('edge_24',):-47,('edge_25',):-47},'current delta')
 require(dn=={('edge_2',):1,('edge_10',):1,('edge_20',):-47,('edge_31',):-49},'next delta')
 # Expand the actual residuals at raw selectors, actual B and actual P.
 cuts=raw|{'radix_86','scale_89'}
 ro=expand(old,'norm_residual1',cuts);rn=expand(new,'norm_residual1',cuts)
 dr=add(add(mul({('radix_86',):1},dn),dc,-1),{('scale_89',):49})
 require(add(rn,ro,-1)==dr,'exact full control residual correction')
 return dict(actual_hat_words=all_words,current_delta=record(dc),next_delta=record(dn),control_residual_delta=record(dr))

def finalizer(rows):
 cuts={'sparse_all_units'}|{f'norm_residual{i}'for i in range(6)}
 p=expand(rows,OUTPUT,cuts);expected={():-1,('sparse_all_units',):1}
 for i in range(6):expected[tuple(sorted(('sparse_all_units',f'norm_residual{i}',f'norm_residual{i}')))]=1
 require(p==expected,'whole finalizer polynomial')
 return p

def degrees(rows,ports):
 cuts=['native__wn2','native__R12','native__R10a','native__gam','native__a4m5'];X,a,c,G,H=cuts
 p=expand(rows,'native__R15',set(cuts));expected={tuple(sorted(m)):v for m,v in [((X,X),1),((a,c,X),2),((X,G),2),((a,c,G),2),((G,G),1),((H,c,c),-1)]}
 require(p==expected,'literal six-term norm cancellation')
 raw={n:1 for n in ports};bound=raw.copy();weights={}
 for n,o,a,b in rows:
  for e in(raw,bound):
   x,y=(0 if type(v)is int else e[v]for v in(a,b));e[n]=x+y if o=='*'else max(x,y)
  if n=='native__R15':
   weights={k:bound[k]for k in cuts};bound[n]=max(sum(weights[k]for k in m)for m in p)
 require([weights[n]for n in cuts]==[308,374,67,375,374],'norm cut degrees')
 require(bound['native__R15']==816 and bound['sparse_all_units']==4993 and bound['norm_sum5']==98 and bound[OUTPUT]==5091 and raw[OUTPUT]==5157,'whole guarded degree')
 require(bound['norm_residual1']==2,'new control degree')
 return dict(norm_coefficients=record(p),norm_cut_degrees=weights,main_norm_bound=816,native_product_bound=4993,outer_sos_bound=98,full_upper=5091,naive_upper=5157,new_control_upper=2,exact_degree_claimed=False)

def build(root,author):
 require(len(AUTHOR_PINS)==3,'final author pins required')
 for base,pins in[(root,PINS),(author,AUTHOR_PINS)]:
  for n,h in pins.items():require(sha((base/n).read_bytes())==h,'pin '+n)
 par=load(root/'residue_affine_sparse_shared471.json');auth=load(author/'residue_affine_sparse_recoded468.json')
 for n,h in auth['dependencies'].items():require(sha((root/n).read_bytes())==h,'author dependency '+n)
 require(par['source_sha256']==PINS['residue_affine_sparse_shared471.py']and auth['source_sha256']==AUTHOR_PINS['residue_affine_sparse_recoded468.py'],'helper bindings')
 p,c=par['packet'],auth['packet'];old,new=p['source'],c['source'];before=serial(par);ports=p['parameters']+p['witnesses']
 require(p['source_sha256']==sha(serial(old))and c['source_sha256']==sha(serial(new)),'literal array hashes')
 for key in['parameters','fixed_program_parameters','ordinary_input_parameter','witnesses','output','literal_height_radix_rows','polynomial_degree_upper_bound','exact_degree_claimed']:require(c[key]==p[key],'interface '+key)
 require(len(ports)==69 and len(c['witnesses'])==67 and c['parameters']==['program','input'],'actual one-program interface')
 require(audit(old,ports)==[471,175,296]and audit(new,ports)==[468,171,297],'full counts')
 od,nd=table(old),table(new);roots=['sparse_all_units']+[f'norm_residual{i}'for i in(0,2,3,4,5)];base=closure(od,roots)&set(od)
 require(len(base)==389 and base==set(auth['source_recipe']['base_names']),'independent base closure')
 require(all(nd[n]==od[n]for n in base),'all389 base definitions unchanged')
 bc=Counter(od[n][1]for n in base);require([bc['*'],bc['+']+bc['-']]==[142,247],'retained base ledger')
 finals=old[-20:];require(all(nd[r[0]]==r for r in finals if r[0]!='norm_residual1'),'other19 finalizer definitions unchanged')
 require(len([n for n in od if n.startswith('native__')])==72 and all(nd[n]==r for n,r in od.items()if n.startswith('native__')),'all72 native rows literal')
 for r in p['literal_height_radix_rows']:require(nd[r[0]]==r,'height/radix literal')
 require({n for n in nd if n not in od}=={n for n in nd if n.startswith('recode_')}and len(set(nd)-set(od))==64,'exact64 new control rows')
 removed=set(od)-set(nd);require(len(removed)==67,'exact67 removed control rows')
 require(all(all(v not in removed for v in r[2:])for n,r in nd.items()),'removed private control closure')
 f=load(root/'residue_affine_sparse_factored.json');program=f['default_table'];primes=f['default_primes'];edges=reconstruct_edges(program,primes)
 require(len(program)==21 and primes==[5,3,2,7,11,13,17,19]and len(edges)==36 and edges==f['edges']==auth['literal_edges'],'literal machine/edge reconstruction')
 require(auth['literal_program']==program and auth['literal_primes']==primes,'literal source data')
 cs=load(root/'residue_affine_sparse_control_codes.json')['state_codes'];require([cs[str(i)]for i in range(23)]==auth['old_state_codes']==OLD_CODES and auth['new_state_codes']==NEW_CODES,'actual code vectors')
 for code in(OLD_CODES,NEW_CODES):require(code[0]==0 and len(set(code))==23 and 0<min(code[1:])and max(code)<192,'injective bounded code criterion')
 plan=auth['plan'];weights={int(k):v for k,v in plan['prime_weights'].items()};correction={int(k):v for k,v in plan['corrections'].items()}
 derived=[0]+[weights[primes[row[1]]]+plan['increment_coefficient']*(row[0]=='I')+correction.get(q,0)for q,row in enumerate(program,1)]+[plan['halt_code']]
 require(derived==NEW_CODES,'exact selected recipe')
 raw={f'edge_{i}'for i in range(36)}
 expected_basis=[(1,list(range(36))),(4,[2,6,8,11]),(1,[5,8,9]),(31,[18,19]),(1,[24,25])]
 for item,(co,ids)in zip(auth['source_recipe']['target_basis'],expected_basis):
  require(item['coefficient']==co and item['indices']==ids and item['register']in base,'paid target basis metadata')
  require(expand(old,item['register'],raw)=={(f'edge_{i}',):1 for i in ids},'paid target basis actual expression')
 require(len(auth['source_recipe']['target_basis'])==5,'complete five-term basis')
 iface=c['control_interfaces'];words=controls(old,new,edges,iface);fo=finalizer(old);fn=finalizer(new);require(fo==fn,'same formal full finalizer')
 require(nd[iface['left']]==[iface['left'],'*','radix_86',iface['following']]and nd[iface['halt']]==[iface['halt'],'*',14,'scale_89']and nd[iface['right']]==[iface['right'],'+',iface['current'],iface['halt']]and nd['norm_residual1']==['norm_residual1','-',iface['left'],iface['right']],'literal new code equation')
 degree=degrees(new,ports);require(c['ledger']==dict(operations=468,multiplications=171,additions_subtractions=297,witnesses=67),'reported full ledger')
 certificate=[r for r in new if r[0]not in {r[0]for r in finals}];count=Counter(r[1]for r in certificate)
 require([len(certificate),count['*'],count['+']+count['-']]==[448,164,284],'full certificate count')
 require(serial(par)==before,'inert parent unchanged')
 return dict(status='PASS_INDEPENDENT_U21_RECODED468',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,parent_pins=PINS,
  rows_checked=468,ledger=[468,171,297],certificate=[448,164,284],ports=69,witnesses=67,base_literal=389,native_literal=72,other_finalizer_literal=19,new_control_rows=64,removed_control_rows=67,
  literal_edges=edges,old_codes=OLD_CODES,new_codes=NEW_CODES,control_proof=words,finalizer_polynomial=record(fo),degree=degree,
  full_output_identity='F_new-F_old=U*(r_new^2-r_old^2); U and every noncontrol residual unchanged',
  positive_scope='Identical supplied positive zeros using inherited control-independent native typing, then bounded injective digit chronology. No all-value equality, new accepting history or exact degree claim.')
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--author-root',type=Path,default=Path('/tmp'));g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=build(a.root,a.author_root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:require(serial(r)==serial(load(a.expect)),'type-exact review receipt')
 print(r['status'],r['ledger'],'degree <=5091')
if __name__=='__main__':main()
