"""Standalone two-program U21 code recoding from the actual470 source; predecessors inert."""
import argparse,hashlib,json,random
from collections import Counter,deque
from pathlib import Path
PINS={
 'residue_affine_sparse_shared470.py':'6705f2abfc330427f47aaf8ee3cbad25ca311e86014e0499c994fdf90b97a586',
 'residue_affine_sparse_shared470.json':'2f7715aa5449118cfad292595bc7cde374587723a123b3c69a0d180cb51993e4',
 'residue_affine_sparse_shared470.md':'b50e62d1eedef24ef390562c70cca69bbbb4b2dd5d6c7f1134ed99b4fb278570',
 'residue_affine_sparse_program_radix504.md':'4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549',
 'residue_affine_sparse_factored.json':'39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda',
 'residue_affine_sparse_factored.md':'b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7',
 'residue_affine_sparse_control_codes.json':'2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d',
 'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
 'residue_affine_sparse_terminal537.md':'9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1',
 'residue_affine_sparse_scale538.md':'0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623'}
WEIGHTS={2:0,3:1,5:2,7:3,11:8,13:9,17:17,19:11}
CORRECTIONS={9:1,11:16,12:32,13:32,14:1,18:16}
BASIS=[(1,list(range(36))),(4,[2,6,8,11]),(1,[5,8,9]),(31,[18,19]),(1,[24,25])]
ALPHA=4;HALT=14;OUT='norm_output';ZERO=(0,)*36

def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def unique(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def bad(x):raise ValueError('noninteger/nonfinite JSON '+x)
def read(p):return json.loads(p.read_text(),object_pairs_hook=unique,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  need(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  need(type(n)is str and n not in d and o in ('+','-','*'),'unique binary row')
  need(all(type(x)in(int,str)for x in(a,b)),'operand type');d[n]=r
 return d
def ancestors(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n in d and n not in seen:seen.add(n);todo.extend(d[n][2:])
 return seen
def ports(rows):
 d=table(rows);return sorted({x for r in rows for x in r[2:]if type(x)is str and x not in d})
def audit(rows,free):
 d=table(rows);seen=set(free)
 for n,o,a,b in rows:
  need(n not in seen and all(type(x)is int or x in seen for x in(a,b)),'acyclic available operands');seen.add(n)
 need(ancestors(d,[OUT])==set(d),'all rows live');need(ports(rows)==sorted(free),'all and only original free ports')
 c=Counter(r[1]for r in rows);return dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'])
def vectors(rows):
 v={f'edge_{i}':tuple(int(i==k)for k in range(36))for i in range(36)}
 for n,o,a,b in rows:
  if n in v:continue
  if o in ('+','-')and a in v and b in v:v[n]=tuple(x+(y if o=='+'else-y)for x,y in zip(v[a],v[b]))
  elif o=='*':
   if type(a)is int and b in v:v[n]=tuple(a*x for x in v[b])
   elif type(b)is int and a in v:v[n]=tuple(b*x for x in v[a])
 return v

class Emitter:
 def __init__(self,base,reserved):
  self.rows=[];self.v=vectors(base);self.cache={v:n for n,v in self.v.items()};self.reserved=set(reserved);self.serial=0
 def op(self,o,a,b):
  if o=='+'and(a==0 or b==0):return b if a==0 else a
  if o=='-'and b==0:return a
  if o=='*'and(a==0 or b==0):return 0
  if o=='*'and(a==1 or b==1):return b if a==1 else a
  if o=='*':
   if type(a)is int and b in self.v:v=tuple(a*x for x in self.v[b])
   elif type(b)is int and a in self.v:v=tuple(b*x for x in self.v[a])
   else:v=None
  else:
   u=ZERO if a==0 else self.v.get(a);w=ZERO if b==0 else self.v.get(b)
   v=tuple(x+(y if o=='+'else-y)for x,y in zip(u,w))if u is not None and w is not None else None
  if v is not None and v in self.cache:return self.cache[v]
  n='recode_'+str(self.serial);self.serial+=1;need(n not in self.reserved,'fresh name');self.reserved.add(n)
  self.rows.append([n,o,a,b])
  if v is not None:self.v[n]=v;self.cache[v]=n
  return n
 def total(self,items):
  out=0
  for a in items:out=self.op('+',out,a)
  return out
 def group(self,ids):
  ids=set(ids);v=tuple(int(i in ids)for i in range(36))
  if v in self.cache:return self.cache[v]
  rest=set(ids);parts=[]
  while rest:
   options=[]
   for n,w in self.v.items():
    if all(x in(0,1)for x in w)and sum(w)>1:
     support={i for i,x in enumerate(w)if x}
     if support<=rest:options.append((len(support),n,support))
   if not options:break
   _,n,s=max(options,key=lambda x:(x[0],x[1]));parts.append(n);rest-=s
  return self.total(parts+[f'edge_{i}'for i in sorted(rest)])
 def signed(self,terms):
  pos=[];neg=[]
  for c,n in terms:
   if c:(pos if c>0 else neg).append(self.op('*',abs(c),n))
  a=self.total(pos);b=self.total(neg);return self.op('-',a,b)if neg else a

def edge_table(program,primes):
 edges=[[0,0,'I',2,1,2,1,2],[0,1,'I',2,1,2,1,2]]
 for q,t in enumerate(program,1):
  op,reg,*targets=t;targets=[v+1 for v in targets];p=primes[reg]
  if op=='I':need(len(targets)==1,'I arity');edges.append([q,targets[0],'I',p,1,p,1,p])
  else:
   need(op in ('D','T')and len(targets)==2,'branch arity')
   edges.append([q,targets[0],op,p,p,1,p,1]if op=='D'else[q,targets[0],op,p,p,p,p,p])
   edges.append([q,targets[1],'Z',p,p,p,1,1])
 return edges

def rebuild(old,edges,codes):
 od=table(old);roots=['sparse_all_units']+[f'norm_residual{i}'for i in(0,2,3,4,5)]
 livebase=ancestors(od,roots);base=[r for r in old if r[0]in livebase];need(len(base)==388,'actual retained base388')
 g=Emitter(base,set(od)|set(ports(old)));vbase=dict(g.v);terms=[]
 for prime,weight in sorted(WEIGHTS.items()):
  if prime!=2 and weight:terms.append((weight,g.group([i for i,e in enumerate(edges)if e[3]==prime])))
 terms.append((ALPHA,g.op('-','action_selector_123','selectors_36')))
 for value in sorted(set(CORRECTIONS.values())):
  terms.append((value,g.group([i for i,e in enumerate(edges)if CORRECTIONS.get(e[0],0)==value])))
 current=g.signed(terms);current_rows=len(g.rows)
 residual=[codes[e[1]]for e in edges];basis=[];basis_checks=[]
 for coefficient,indices in BASIS:
  n=g.group(indices);want=tuple(int(i in indices)for i in range(36))
  need(n in vbase and vbase[n]==want,'target basis is paid in actual retained base')
  basis.append((coefficient,n));basis_checks.append(dict(coefficient=coefficient,indices=indices,register=n,vector=list(want)))
  residual=[x-coefficient*y for x,y in zip(residual,want)]
 terms=[(value,g.group([i for i,x in enumerate(residual)if x==value]))for value in sorted(set(residual)-{0})]
 following=g.signed(terms+basis)
 need(g.v[current]==tuple(codes[e[0]]for e in edges),'current coefficient vector')
 need(g.v[following]==tuple(codes[e[1]]for e in edges),'target coefficient vector')
 left=g.op('*','radix_86',following);halt=g.op('*',HALT,'scale_89');right=g.op('+',current,halt)
 d={r[0]:list(r)for r in base+g.rows}
 for r in old[-20:]:d[r[0]]=list(r)
 d['norm_residual1']=['norm_residual1','-',left,right]
 # Reuse G3+G5 already paid by the global population: G3+2G5=(G3+G5)+G5.
 wanted=tuple(x+2*y for x,y in zip(vbase['prime_selector_93'],vbase['prime_selector_95']))
 target=[n for n,v in g.v.items()if v==wanted and n not in vbase];need(len(target)==1,'current prefix target')
 target=target[0];prior=list(d[target]);d[target]=[target,'+','u21_grouped_J_0','prime_selector_95']
 need(tuple(x+y for x,y in zip(vbase['u21_grouped_J_0'],vbase['prime_selector_95']))==wanted,'paid current prefix identity')
 keep=ancestors(d,[OUT]);dead=sorted(set(d)-keep);need(dead==['recode_5'],'one private scalar producer eliminated')
 out=[];done=set();active=set()
 def emit(n):
  if type(n)is int or n not in d or n not in keep or n in done:return
  need(n not in active,'cycle');active.add(n)
  for x in d[n][2:]:emit(x)
  active.remove(n);done.add(n);out.append(d[n])
 for r in old:
  if r[0]in keep:emit(r[0])
 emit(OUT);need(done==keep,'complete output schedule')
 return out,dict(base_names=sorted(livebase),base_count=len(base),old_private_control=sorted(set(od)-livebase-{r[0]for r in old[-20:]}),
  current=current,following=following,left=left,right=right,halt=halt,target_basis=basis_checks,target_residual_coefficients=residual,
  current_prefix_reuse=dict(target=target,parent_definition=prior,new_definition=d[target],removed=dead),current_provisional_rows=current_rows)

# Sparse integer-polynomial interpreter for bounded local/full-finalizer cones.
def add(a,b,s=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+s*v
 return {m:v for m,v in d.items()if v}
def mul(a,b):
 d={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+v*w
 return {m:v for m,v in d.items()if v}
def expand(rows,target,boundaries):
 d=table(rows);memo={n:{(n,):1}for n in boundaries}
 def at(n):
  if type(n)is int:return {():n}if n else{}
  if n not in memo:
   need(n in d,'polynomial boundary '+n);_,o,a,b=d[n];a,b=at(a),at(b)
   memo[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1);need(len(memo[n])<1000,'bounded polynomial cone')
  return memo[n]
 return at(target)
def plist(p):return [[list(m),v]for m,v in sorted(p.items())]

def contract(old,new,info,edges,oldcodes,codes):
 od,nd=table(old),table(new);base=set(info['base_names'])
 need(all(nd[n]==od[n]for n in base),'all388 base rows literal')
 need(all(nd[r[0]]==r for r in old[-20:]if r[0]!='norm_residual1'),'other19 finalizer rows literal')
 native=[r for r in old if r[0].startswith('native__')];need(len(native)==72 and all(nd[r[0]]==r for r in native),'native72 literal')
 for i in range(36):need(nd[f'edge_{i}']==[f'edge_{i}','-',f'edge{i}_hat',1],'actual supplied hat shift')
 hats={f'edge{i}_hat'for i in range(36)}
 def wordpoly(cs,end):
  v=[cs[e[end]]for e in edges];return {():-sum(v),**{(f'edge{i}_hat',):c for i,c in enumerate(v)if c}}
 oldC='control_codes__current_positive_29';oldN='control_codes__target_difference_70'
 for r in [['control_codes__left_71','*','radix_86',oldN],['control_codes__halt_72','*',oldcodes[22],'scale_89'],['control_codes__right_73','+',oldC,'control_codes__halt_72'],['norm_residual1','-','control_codes__left_71','control_codes__right_73']]:need(od[r[0]]==r,'literal old coded residual')
 for r in [[info['left'],'*','radix_86',info['following']],[info['halt'],'*',codes[22],'scale_89'],[info['right'],'+',info['current'],info['halt']],['norm_residual1','-',info['left'],info['right']]]:need(nd[r[0]]==r,'literal new coded residual')
 expected=[]
 for rows,C,N,cs in[(old,oldC,oldN,oldcodes),(new,info['current'],info['following'],codes)]:
  for name,end in[(C,0),(N,1)]:
   value=expand(rows,name,hats);want=wordpoly(cs,end);need(value==want,'full actual hat control vector');expected.append(dict(register=name,coefficients=plist(value)))
 dc=add(expand(new,info['current'],hats),expand(old,oldC,hats),-1)
 dn=add(expand(new,info['following'],hats),expand(old,oldN,hats),-1)
 edgevars={f'edge_{i}'for i in range(36)}
 expectdc=add(expand(old,'prime_selector_115',edgevars),{('edge_24',):47,('edge_25',):47},-1)
 expectdn={('edge_2',):1,('edge_10',):1,('edge_20',):-47,('edge_31',):-49}
 dce=add(expand(new,info['current'],edgevars),expand(old,oldC,edgevars),-1)
 dne=add(expand(new,info['following'],edgevars),expand(old,oldN,edgevars),-1)
 need(dce==expectdc and dne==expectdn,'compact exact control deltas')
 # Bind each finalizer to U and the actual six residuals; five residuals and U
 # are in the literal base, so those computed values are identical.
 cuts={'sparse_all_units'}|{f'norm_residual{i}'for i in range(6)}
 po=expand(old,OUT,cuts);pn=expand(new,OUT,cuts);need(po==pn,'same formal full finalizer')
 U='sparse_all_units';R='norm_residual1';want={():-1,(U,):1}
 for i in range(6):want[tuple(sorted((U,f'norm_residual{i}',f'norm_residual{i}')))]=1
 need(po==want,'complete U*(1+sum squares)-1 expansion')
 correction={tuple(sorted((U,'new_control_residual','new_control_residual'))):1,
             tuple(sorted((U,'old_control_residual','old_control_residual'))):-1}
 return dict(all388_retained_base_values_identical=True,all_native_rows_literal=72,other_finalizer_rows_literal=19,
  actual_hat_control_words=expected,current_delta_in_edges=plist(dce),target_delta_in_edges=plist(dne),
  finalizer_polynomial=plist(po),full_output_correction=plist(correction),
  identity='F_new-F_old = unchanged_U*(r_new^2-r_old^2), over every commutative ring',
  zero_scope='Identical supplied positive integer zero sets by unchanged typing and injective bounded code chronology; not an all-value polynomial identity')

def degree(rows):
 free=ports(rows);raw={n:1 for n in free}
 for n,o,a,b in rows:
  a=0 if type(a)is int else raw[a];b=0 if type(b)is int else raw[b];raw[n]=a+b if o=='*'else max(a,b)
 names=['native__wn2','native__R12','native__R10a','native__gam'];X,a,c,G=names
 poly=expand(rows,'native__R15',set(names));expected={tuple(sorted(m)):v for m,v in [((X,X),1),((a,c,X),2),((X,G),2),((a,c,G),2),((G,G),1),((a,c,c),-4),((c,c),-3)]}
 need(poly==expected,'main norm exact cancellation');weights={n:raw[n]for n in names};need([weights[n]for n in names]==[312,379,68,380],'computed degree weights')
 bound=max(sum(weights[n]for n in m)for m in poly);need(bound==827,'main norm bound')
 d={n:1 for n in free}
 for n,o,a,b in rows:
  a=0 if type(a)is int else d[a];b=0 if type(b)is int else d[b];d[n]=a+b if o=='*'else max(a,b)
  if n=='native__R15':d[n]=bound
 need(raw[OUT]==5227 and d[OUT]==5160 and d['sparse_all_units']==5062 and d['norm_sum5']==98,'complete degree bounds')
 return dict(polynomial_degree_upper_bound=5160,naive_bound=5227,native_product_bound=5062,outer_SOS_bound=98,control_residual_bound=d['norm_residual1'],norm_expansion=plist(poly),boundary_degree_bounds=weights,exact_degree_claimed=False)

def eval_rows(rows,values,p):
 v=dict(values)
 for n,o,a,b in rows:
  a=v[a]if type(a)is str else a;b=v[b]if type(b)is str else b
  v[n]=(a*b if o=='*'else a+b if o=='+'else a-b)%p
 return v

def chronology(edges,oldcodes,codes):
 def path(start,end):
  todo=deque([(start,[])]);seen={start}
  while todo:
   q,w=todo.popleft()
   if q==end:return w
   for i,e in enumerate(edges):
    if e[0]==q and e[1]not in seen:seen.add(e[1]);todo.append((e[1],w+[i]))
  raise ValueError('unreachable fixture')
 fixtures=[path(0,e[0])+[i]+path(e[1],22)for i,e in enumerate(edges)]
 rng=random.Random(46836);fixtures +=[[rng.randrange(36)for _ in range(rng.randrange(1,9))]for _ in range(200)]
 accepted=0
 for word in fixtures:
  real=edges[word[0]][0]==0 and edges[word[-1]][1]==22 and all(edges[x][1]==edges[y][0]for x,y in zip(word,word[1:]))
  for B in(128,256):
   power=B**len(word)
   for cs in(oldcodes,codes):
    C=sum(cs[edges[i][0]]*B**k for k,i in enumerate(word));N=sum(cs[edges[i][1]]*B**k for k,i in enumerate(word))
    need((B*N-C-cs[22]*power==0)==real,'typed word chronology')
  accepted+=real
 return dict(typed_edge_words=len(fixtures),accepted_words=accepted,bases=[128,256],code_equations_checked=4*len(fixtures),scope='Control words only, not payload histories/native zeros')

def build(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'dependency '+n)
 parent=read(root/'residue_affine_sparse_shared470.json');p=parent['packet'];before=canonical(parent);old=p['source']
 need(parent['source_sha256']==PINS['residue_affine_sparse_shared470.py']and p['source_sha256']==sha(canonical(old)),'parent bindings')
 free=p['parameters']+p['witnesses'];need(len(free)==70 and len(p['witnesses'])==67,'two-program ports')
 need(p['parameters']==['program','radix_program','input']and p['fixed_program_parameters']==['program','radix_program'],'two-program recipe')
 f=read(root/'residue_affine_sparse_factored.json');program=f['default_table'];primes=f['default_primes'];edges=edge_table(program,primes)
 need(len(program)==21 and len(edges)==36 and edges==f['edges']and primes==[5,3,2,7,11,13,17,19],'all literal U21 edges/prime labels')
 oldcodes_record=read(root/'residue_affine_sparse_control_codes.json')['state_codes'];oldcodes=[oldcodes_record[str(q)]for q in range(23)]
 codes=[0]+[WEIGHTS[primes[t[1]]]+ALPHA*(t[0]=='I')+CORRECTIONS.get(q,0)for q,t in enumerate(program,1)]+[HALT]
 need(codes==[0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14],'selected exact codes')
 need(len(set(codes))==23 and min(codes[1:])>=1 and max(codes)==41 and max(codes)<128,'valid injective code range')
 new,info=rebuild(old,edges,codes);prior=audit(old,free);after=audit(new,free)
 need(prior==dict(operations=470,multiplications=175,additions_subtractions=295),'parent ledger')
 need(after==dict(operations=467,multiplications=171,additions_subtractions=296),'complete recoded467 ledger')
 identity=contract(old,new,info,edges,oldcodes,codes);deg=degree(new)
 need(all(table(new)[r[0]]==r for r in p['literal_height_radix_rows']),'literal h=x+eta/B=C*h')
 final_names={r[0]for r in old[-20:]};certificate=[r for r in new if r[0]not in final_names];cc=Counter(r[1]for r in certificate)
 cle=dict(operations=len(certificate),multiplications=cc['*'],additions_subtractions=cc['+']+cc['-'],equations=7,witnesses=67)
 need(cle==dict(operations=447,multiplications=164,additions_subtractions=283,equations=7,witnesses=67),'certificate447')
 rng=random.Random(46820261004)
 for prime in(1000000007,1000000009):
  for _ in range(16):
   v={n:rng.randrange(-31,32)for n in free};a,b=eval_rows(old,v,prime),eval_rows(new,v,prime)
   need(all(a[n]==b[n]for n in info['base_names']),'literal base diagnostics')
   need((b[OUT]-a[OUT])%prime==a['sparse_all_units']*(b['norm_residual1']**2-a['norm_residual1']**2)%prime,'complete output correction')
 need(canonical(parent)==before,'inert parent unchanged in memory')
 packet={k:v for k,v in p.items()if k not in ('source','source_sha256','ledger','certificate_ledger')}
 packet['ordinary_input_parameter']='input'
 packet['valid_recipe']='Fixed E=3^e; C is dyadic, C>=64 and C>E; B=C*(x+height_slack). Selected recoded plan has maximum code41, below B>=128.'
 packet.update(source=new,source_sha256=sha(canonical(new)),ledger=dict(after,witnesses=67),certificate_ledger=cle,control_interfaces={k:info[k]for k in('current','following','left','right','halt')})
 return dict(status='PASS_U21_RECODED467',source_sha256=sha(Path(__file__).read_bytes()),dependencies=PINS,packet=packet,
  literal_program=program,literal_primes=primes,literal_edges=edges,old_state_codes=oldcodes,new_state_codes=codes,
  plan=dict(prime_weights={str(k):v for k,v in WEIGHTS.items()},increment_coefficient=ALPHA,corrections={str(k):v for k,v in CORRECTIONS.items()},halt_code=HALT,target_basis=BASIS),
  source_recipe=info,exact_contract=identity,degree_proof=deg,
  finite_checks=dict(signed_full_source_corrections=32,chronology=chronology(edges,oldcodes,codes),native_zero_materialized=False),
  scope='Actual two-program470 to467 recoding on valid fixed E=3^e,C dyadic>=64,C>E slices with ordinary positive x. Identical supplied positive zeros through unchanged typing plus bounded injective control codes. Full outputs related by explicit correction, not identical. No positive-coordinate map to one-program sources, circuit minimum, exact degree or below84 claim.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:need(canonical(read(a.expect))==canonical(r),'exact type-sensitive receipt')
 print(r['status'],r['packet']['ledger'],'degree <=5160')
if __name__=='__main__':main()
