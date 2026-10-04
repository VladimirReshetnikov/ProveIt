"""Fresh two-interface joint U21 recoding; all frozen dependencies inert."""
import argparse,hashlib,json,random
from collections import Counter,deque
from pathlib import Path
PINS={
 'residue_affine_sparse_recoded468.py':'4b73c18e91473205dfb50edaf3e289898af305b14781ca1e10ce8a2ec06d834f',
 'residue_affine_sparse_recoded468.json':'1aa26a73ebce4e5a8cfeb443b7d2aa296bbf7816a5c842728f6a3862872936b4',
 'residue_affine_sparse_recoded468.md':'93607b73b03769c46ec698c2b2d1bac83e3c192e81c9d29d4d000de66ef35ea7',
 'residue_affine_sparse_recoded467.py':'08bea80dc49d502171f3786cf11c6e0b5b959c4812d8086543e4e66fc9ab4039',
 'residue_affine_sparse_recoded467.json':'9b816825cfa560db664c2d262fd2a4815b2f28046f8d500675e6a38d5d48af70',
 'residue_affine_sparse_recoded467.md':'adba76e7aa7d6155b0f568c9a83ecc6859536b65b150b63b60a06ffdf1d0acbd',
 'residue_affine_sparse_factored.json':'39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda',
 'residue_affine_sparse_program_radix504.md':'4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549',
 'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
 'residue_affine_sparse_terminal537.md':'9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1',
 'residue_affine_sparse_scale538.md':'0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623'}
WEIGHTS={2:0,3:1,5:2,7:3,11:8,13:9,17:17,19:11}
CORRECTIONS={9:1,11:29,12:21,13:32,14:1,18:32}
BASIS=[(1,'selectors_70',list(range(36))),(4,'action_selector_126',[2,6,8,11]),
       (1,'prime_selector_111',[5,8,9]),(29,'control_codes__duplicate_state_2',[18,19]),
       (1,'control_codes__duplicate_state_8',[24,25])]
CODES=[0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14]
OLD_CODES=[0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14]
OUT='norm_output';ZERO=(0,)*36

def check(ok,msg):
 if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(path):
 def pairs(xs):
  out={}
  for k,v in xs:check(k not in out,'duplicate JSON key');out[k]=v
  return out
 def bad(v):raise ValueError('noninteger/nonfinite JSON '+v)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(rows):
 out={}
 for r in rows:
  check(type(r)is list and len(r)==4,'literal row shape');n,o,a,b=r
  check(type(n)is str and n not in out and o in ('+','-','*'),'SSA opcode')
  check(type(a)in(int,str)and type(b)in(int,str),'operand types');out[n]=r
 return out
def closure(defs,roots):
 live=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n in defs and n not in live:live.add(n);todo.extend(defs[n][2:])
 return live
def audit(rows,free):
 defs=table(rows);seen=set(free);used=set()
 for n,o,a,b in rows:
  check(n not in seen and all(type(x)is int or x in seen for x in (a,b)),'topological paid operands')
  used.update(x for x in(a,b)if type(x)is str);seen.add(n)
 check(closure(defs,[OUT])==set(defs),'all rows live')
 check(used-set(defs)==set(free),'all and only supplied ports live')
 c=Counter(r[1]for r in rows)
 return {'operations':len(rows),'multiplications':c['*'],'additions_subtractions':c['+']+c['-']}
def vadd(a,b,s=1):return tuple(x+s*y for x,y in zip(a,b))
def vmul(v,c):return tuple(c*x for x in v)
def bits(v):return sum(1<<i for i,x in enumerate(v)if x)
def vectors(rows):
 v={f'edge_{i}':tuple(int(i==j)for j in range(36))for i in range(36)}
 for n,o,a,b in rows:
  if n in v:continue
  if o in ('+','-')and a in v and b in v:v[n]=vadd(v[a],v[b],1 if o=='+'else-1)
  elif o=='*':
   if type(a)is int and b in v:v[n]=vmul(v[b],a)
   elif type(b)is int and a in v:v[n]=vmul(v[a],b)
 return v
class Emit:
 def __init__(self,base):
  self.rows=[];self.v=vectors(base);self.cache={v:n for n,v in self.v.items()};self.groups=[];self.pair={}
  self.paid=dict(self.v)
  for n,v in self.v.items():
   if all(x in(0,1)for x in v)and sum(v)>1:self.groups.append((sum(v),n,bits(v)))
  for n,a in self.v.items():
   for m,b in self.v.items():
    for o,k in [('+',1),('-',-1)]:
     v=vadd(a,b,k)
     if v not in self.cache:self.pair.setdefault(v,(o,n,m))
 def op(self,o,a,b):
  if o=='+'and (a==0 or b==0):return b if a==0 else a
  if o=='-'and b==0:return a
  if o=='*'and (a==0 or b==0):return 0
  if o=='*'and (a==1 or b==1):return b if a==1 else a
  v=None
  if o in ('+','-'):
   u=ZERO if a==0 else self.v.get(a);w=ZERO if b==0 else self.v.get(b)
   if u is not None and w is not None:v=vadd(u,w,1 if o=='+'else-1)
  elif type(a)is int and b in self.v:v=vmul(self.v[b],a)
  elif type(b)is int and a in self.v:v=vmul(self.v[a],b)
  if v is not None:
   if v==ZERO:return 0
   if v in self.cache:return self.cache[v]
   if v in self.pair:o,a,b=self.pair[v]
  n='joint_'+str(len(self.rows));self.rows.append([n,o,a,b])
  if v is not None:
   self.v[n]=v;self.cache[v]=n
   if all(x in (0,1)for x in v)and sum(v)>1:self.groups.append((sum(v),n,bits(v)))
  return n
 def total(self,items):
  out=0
  for a in items:out=self.op('+',out,a)
  return out
 def group(self,indices):
  ids=set(indices);v=tuple(int(i in ids)for i in range(36))
  if v==ZERO:return 0
  if v in self.cache:return self.cache[v]
  rest=bits(v);pieces=[]
  while rest:
   choices=[g for g in self.groups if g[2]&rest==g[2]]
   if not choices:break
   _,n,mask=max(choices);pieces.append(n);rest^=mask
  return self.total(pieces+[f'edge_{i}'for i in range(36)if rest>>i&1])
 def signed(self,terms):
  # Coefficients are fixed literals, but each nontrivial use is charged.
  pos=[];neg=[]
  for c,n in terms:
   if c and n!=0:(pos if c>0 else neg).append(self.op('*',abs(c),n))
  a=self.total(pos);b=self.total(neg)
  return self.op('-',a,b)if neg else a

def edges_from_table(program,primes):
 edges=[[0,0,'I',2,1,2,1,2],[0,1,'I',2,1,2,1,2]]
 for q,t in enumerate(program,1):
  op,reg,*dest=t;p=primes[reg];dest=[v+1 for v in dest]
  if op=='I':
   check(len(dest)==1,'increment arity');edges.append([q,dest[0],'I',p,1,p,1,p])
  else:
   check(op in ('D','T')and len(dest)==2,'test arity')
   edges.append([q,dest[0],op,p,p,1,p,1]if op=='D'else[q,dest[0],op,p,p,p,p,p])
   edges.append([q,dest[1],'Z',p,p,p,1,1])
 return edges

def emit(old,edges,free,base_size):
 od=table(old);base_names=closure(od,['sparse_all_units']+[f'norm_residual{i}'for i in(0,2,3,4,5)])
 base=[r for r in old if r[0]in base_names]
 check(len(base)==base_size,'actual complete retained base')
 tail=[r for r in old if r[0].startswith('norm_')and r[0]not in base_names]
 check(len(tail)==15,'remaining complete finalizer')
 g=Emit(base);terms=[]
 for p,w in sorted(WEIGHTS.items()):
  if p!=2 and w:terms.append((w,g.group(i for i,e in enumerate(edges)if e[3]==p)))
 terms.append((4,g.op('-','action_selector_123','selectors_36')))
 for c in sorted(set(CORRECTIONS.values())):
  terms.append((c,g.group(i for i,e in enumerate(edges)if CORRECTIONS.get(e[0],0)==c)))
 current=g.signed(terms)
 rem=[CODES[e[1]]for e in edges];basis=[];paid_basis=[]
 for c,name,ids in BASIS:
  wanted=tuple(int(i in ids)for i in range(36))
  check(g.paid[name]==wanted,'actual paid target basis '+name)
  basis.append((c,name));rem=[a-c*b for a,b in zip(rem,wanted)]
  paid_basis.append({'coefficient':c,'register':name,'vector':list(wanted)})
 terms=[(c,g.group(i for i,x in enumerate(rem)if x==c))for c in sorted(set(rem)-{0})]
 following=g.signed(terms+basis)
 check(g.v[current]==tuple(CODES[e[0]]for e in edges),'all36 current coefficients')
 check(g.v[following]==tuple(CODES[e[1]]for e in edges),'all36 target coefficients')
 hc=g.op('*',14,'scale_89');left=g.op('*','radix_86',following);right=g.op('+',current,hc)
 defs=table(base+g.rows+tail);defs['norm_residual1']=['norm_residual1','-',left,right]
 keep=closure(defs,[OUT]);out=[];done=set(free);active=set()
 def visit(n):
  if type(n)is int or n in done:return
  check(n in defs and n not in active,'new cycle/undefined wire');active.add(n)
  for a in defs[n][2:]:visit(a)
  active.remove(n);done.add(n);out.append(defs[n])
 for r in old:
  if r[0]in keep:visit(r[0])
 visit(OUT);check({r[0]for r in out}==keep,'complete emitted source')
 info={'base_count':len(base),'base_names':sorted(base_names),'base_source':base,
       'new_control_rows':[r for r in out if r[0].startswith('joint_')],
       'paid_target_basis':paid_basis,'target_residual_coefficients':rem,
       'interfaces':dict(current=current,following=following,halt=hc,left=left,right=right),
       'provisional_dead_rows':[r for r in g.rows if r[0]not in keep]}
 return out,info

def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items()if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items()if c}
def expand(rows,target,cuts):
 defs=table(rows);memo={n:{(n,):1}for n in cuts}
 def at(n):
  if type(n)is int:return {():n}if n else{}
  if n not in memo:
   check(n in defs,'unbound cut '+n);_,o,a,b=defs[n];a,b=at(a),at(b)
   memo[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1)
   check(len(memo[n])<3000,'bounded sparse cone')
  return memo[n]
 return at(target)
def serial(p):return [[list(m),c]for m,c in sorted(p.items())]

def contract(old,new,old_interfaces,info,edges):
 od,nd=table(old),table(new);base=set(info['base_names']);ci=info['interfaces']
 check(all(nd[n]==od[n]for n in base),'every retained base definition literal')
 native=[r for r in old if r[0].startswith('native__')]
 check(len(native)==72 and all(nd[r[0]]==r for r in native),'native72 literal')
 finals=[r for r in old if r[0].startswith('norm_')]
 # The six residual producers and fourteen remaining finalizer rows.
 check(len(finals)==20 and all(nd[r[0]]==r for r in finals if r[0]!='norm_residual1'),'other19 finalizer/residual rows literal')
 for i in range(36):check(nd[f'edge_{i}']==[f'edge_{i}','-',f'edge{i}_hat',1],'actual positive hat shift')
 hats={f'edge{i}_hat'for i in range(36)};words=[]
 for rows,ints,codes in[(old,old_interfaces,OLD_CODES),(new,ci,CODES)]:
  for name,end in[(ints['current'],0),(ints['following'],1)]:
   cs=[codes[e[end]]for e in edges];expected={():-sum(cs),**{(f'edge{i}_hat',):c for i,c in enumerate(cs)if c}}
   actual=expand(rows,name,hats);check(actual==expected,'all36 actual-hat coefficients')
   words.append({'register':name,'coefficients':serial(actual)})
  for row in [[ints['left'],'*','radix_86',ints['following']],
              [ints['halt'],'*',14,'scale_89'],[ints['right'],'+',ints['current'],ints['halt']],
              ['norm_residual1','-',ints['left'],ints['right']]]:
   check(table(rows)[row[0]]==row,'literal control boundary')
 edgecuts={f'edge_{i}'for i in range(36)}
 dc=add(expand(new,ci['current'],edgecuts),expand(old,old_interfaces['current'],edgecuts),-1)
 dn=add(expand(new,ci['following'],edgecuts),expand(old,old_interfaces['following'],edgecuts),-1)
 expected_dc={(f'edge_{i}',):c for i,c in [(18,13),(19,13),(20,-11),(21,-11),(30,16),(31,16)]}
 expected_dn={(f'edge_{i}',):c for i,c in [(17,13),(28,13),(18,-11),(22,16),(26,16),(33,16),(35,16)]}
 check(dc==expected_dc and dn==expected_dn,'exact state-change deltas')
 boundary=edgecuts|{'radix_86','scale_89'}
 dr=add(expand(new,'norm_residual1',boundary),expand(old,'norm_residual1',boundary),-1)
 check(dr==add(mul({('radix_86',):1},dn),dc,-1),'actual complete control correction')
 U='sparse_all_units';cuts={U}|{f'norm_residual{i}'for i in range(6)}
 final=expand(new,OUT,cuts);check(final==expand(old,OUT,cuts),'complete formal finalizers')
 want={():-1,(U,):1}
 for i in range(6):want[tuple(sorted((U,f'norm_residual{i}',f'norm_residual{i}')))]=1
 check(final==want,'full U times SOS plus1 minus1')
 # Expand the complete outer correction after binding all five common residuals
 # and U to their literally equal upstream values.
 oldr={('old_control',):1};delta={('control_delta',):1};newr=add(oldr,delta)
 correction=mul({(U,):1},add(mul(newr,newr),mul(oldr,oldr),-1))
 check(correction=={tuple(sorted((U,'old_control','control_delta'))):2,
                    tuple(sorted((U,'control_delta','control_delta'))):1},'exact final correction')
 word_ledgers=[]
 for rows,ints in[(old,old_interfaces),(new,ci)]:
  defs=table(rows);cset=closure(defs,[ints['current']])-base;nset=closure(defs,[ints['following']])-base
  def count(names):
   c=Counter(defs[n][1]for n in names)
   return {'operations':len(names),'multiplications':c['*'],'additions_subtractions':c['+']+c['-']}
  word_ledgers.append({'current':count(cset),'target':count(nset),'union':count(cset|nset),'shared_rows':[defs[n]for n in sorted(cset&nset)]})
 check(word_ledgers[0]['union']==dict(operations=61,multiplications=20,additions_subtractions=41),'old61 word ledger')
 check(word_ledgers[1]['union']==dict(operations=60,multiplications=20,additions_subtractions=40),'new60 word ledger')
 check(word_ledgers[1]['shared_rows']==[['joint_12','*',29,'control_codes__duplicate_state_2']],'actual shared29 product')
 check(nd['joint_26']==['joint_26','-','remainder_total_coefficient_group_160','edge_7'],'paid three-edge remainder prefix')
 return {'all_base_values_identical':len(base),'native_rows_literal':72,'other_final_rows_literal':19,
         'actual_hat_words':words,'current_delta_in_edges':serial(dc),'target_delta_in_edges':serial(dn),
         'control_delta_in_edges':serial(dr),'formal_finalizer':serial(final),'full_output_correction':serial(correction),
         'old_new_word_ledgers':word_ledgers,
         'identity':'F_new-F_old=U*(2*r_old*delta_r+delta_r^2), delta_r=B*delta_N-delta_C',
         'scope':'All-ring correction at identical supplied coordinates; positive-zero equivalence separately uses native typing and code chronology'}

def degree(rows,two):
 free=sorted({x for r in rows for x in r[2:]if type(x)is str}-{r[0]for r in rows})
 raw={n:1 for n in free}
 for n,o,a,b in rows:
  a=raw[a]if type(a)is str else 0;b=raw[b]if type(b)is str else 0;raw[n]=a+b if o=='*'else max(a,b)
 X,a,c,G=['native__wn2','native__R12','native__R10a','native__gam'];names=[X,a,c,G]
 poly=expand(rows,'native__R15',set(names))
 expected={tuple(sorted(m)):v for m,v in [((X,X),1),((a,c,X),2),((G,X),2),((a,c,G),2),((G,G),1),((a,c,c),-4),((c,c),-3)]}
 check(poly==expected,'exact main-norm cancellation at actual cuts')
 weights={n:raw[n]for n in names};check(list(weights.values())==([312,379,68,380]if two else[308,374,67,375]),'actual degree cut weights')
 bound=max(sum(weights[n]for n in m)for m in poly);check(bound==(827 if two else 816),'guarded norm bound')
 d={n:1 for n in free}
 for n,o,a,b in rows:
  a=d[a]if type(a)is str else 0;b=d[b]if type(b)is str else 0;d[n]=a+b if o=='*'else max(a,b)
  if n=='native__R15':d[n]=bound
 check((d[OUT],raw[OUT],d['sparse_all_units'],d['norm_sum5'],d['norm_residual1'])==((5160,5227,5062,98,3)if two else(5091,5157,4993,98,2)),'full propagated bounds')
 return {'polynomial_degree_upper_bound':d[OUT],'naive_bound':raw[OUT],'native_product_bound':d['sparse_all_units'],
         'outer_SOS_bound':d['norm_sum5'],'control_residual_bound':d['norm_residual1'],'main_norm_bound':bound,
         'actual_cut_weights':weights,'main_norm_polynomial':serial(poly),'exact_degree_claimed':False}

def evaluate(rows,ports,prime):
 values=dict(ports)
 for n,o,a,b in rows:
  a=values[a]if type(a)is str else a;b=values[b]if type(b)is str else b
  values[n]=(a*b if o=='*'else a+b if o=='+'else a-b)%prime
 return values

def chronology(edges):
 def path(start,end):
  queue=deque([(start,[])]);seen={start}
  while queue:
   s,word=queue.popleft()
   if s==end:return word
   for i,e in enumerate(edges):
    if e[0]==s and e[1]not in seen:seen.add(e[1]);queue.append((e[1],word+[i]))
  raise ValueError('unreachable control path')
 words=[path(0,e[0])+[i]+path(e[1],22)for i,e in enumerate(edges)]
 rng=random.Random(467466);words +=[[rng.randrange(36)for _ in range(rng.randrange(1,10))]for _ in range(200)]
 records=[]
 for word in words:
  good=edges[word[0]][0]==0 and edges[word[-1]][1]==22 and all(edges[i][1]==edges[j][0]for i,j in zip(word,word[1:]))
  for B in(128,192,256):
   for codes in(OLD_CODES,CODES):
    C=sum(codes[edges[i][0]]*B**k for k,i in enumerate(word));N=sum(codes[edges[i][1]]*B**k for k,i in enumerate(word))
    check((B*N-C-codes[-1]*B**len(word)==0)==good,'typed finite chronology')
  records.append({'word':word,'chronological':good})
 return {'records':records,'bases':[128,192,256],'equations_checked':6*len(words),'scope':'Typed control words, not payload computations or complete native Pell zeros'}

def build(root):
 for name,pin in PINS.items():check(sha((root/name).read_bytes())==pin,'dependency '+name)
 data=read(root/'residue_affine_sparse_factored.json');program=data['default_table'];primes=data['default_primes']
 edges=edges_from_table(program,primes)
 check(len(program)==21 and len(edges)==36 and edges==data['edges']and primes==[5,3,2,7,11,13,17,19],'complete actual U21 table and labels')
 codes=[0]+[WEIGHTS[primes[t[1]]]+4*(t[0]=='I')+CORRECTIONS.get(q,0)for q,t in enumerate(program,1)]+[14]
 check(codes==CODES and len(set(codes))==23 and min(codes[1:])==1 and max(codes)==40,'selected valid exact codes')
 packets=[]
 for two,stem in [(False,'residue_affine_sparse_recoded468'),(True,'residue_affine_sparse_recoded467')]:
  ancestor=read(root/(stem+'.json'));before=canonical(ancestor);p=ancestor['packet'];old=p['source'];free=p['parameters']+p['witnesses']
  check(ancestor['source_sha256']==PINS[stem+'.py']and p['source_sha256']==sha(canonical(old)),'parent byte/source bindings')
  check(ancestor['new_state_codes']==OLD_CODES and ancestor['literal_edges']==edges,'literal immediate parent codes/table')
  parameters=['program','radix_program','input']if two else['program','input']
  fixed=['program','radix_program']if two else['program']
  height=[['height_85','+','input','height_slack'],['radix_86','*','radix_program','height_85']]if two else[
          ['height_83','+','program','input'],['height_85','+','height_83','height_slack'],['radix_86','*',64,'height_85']]
  check(p['parameters']==parameters and p['fixed_program_parameters']==fixed and p['ordinary_input_parameter']=='input','distinct supplied interfaces')
  check(len(p['witnesses'])==67 and len(free)==(70 if two else 69),'complete ports')
  check(p['literal_height_radix_rows']==height and all(table(old)[r[0]]==r for r in height),'actual height/radix recipe')
  new,info=emit(old,edges,free,388 if two else 389)
  check(all(table(new)[r[0]]==r for r in height),'height/radix unchanged')
  oldledger=audit(old,free);ledger=audit(new,free)
  check(oldledger==dict(operations=467 if two else 468,multiplications=171,additions_subtractions=296 if two else 297),'parent complete ledger')
  check(ledger==dict(operations=466 if two else 467,multiplications=171,additions_subtractions=295 if two else 296),'new complete ledger')
  check(len(info['new_control_rows'])==63,'complete63 control rows beyond base')
  cert=[r for r in new if not r[0].startswith('norm_')];cc=Counter(r[1]for r in cert)
  certificate={'operations':len(cert),'multiplications':cc['*'],'additions_subtractions':cc['+']+cc['-'],'equations':7,'witnesses':67}
  check(certificate==dict(operations=446 if two else 447,multiplications=164,additions_subtractions=282 if two else 283,equations=7,witnesses=67),'complete certificate ledger')
  proof=contract(old,new,p['control_interfaces'],info,edges);deg=degree(new,two)
  rng=random.Random(467466+two);checks=[]
  for prime in(1000000007,1000000009):
   for _ in range(16):
    vals={n:rng.randrange(-31,32)for n in free};a,b=evaluate(old,vals,prime),evaluate(new,vals,prime)
    check(all(a[n]==b[n]for n in info['base_names']),'all retained base values diagnostic')
    check((b[OUT]-a[OUT])%prime==a['sparse_all_units']*(b['norm_residual1']**2-a['norm_residual1']**2)%prime,'whole source correction diagnostic')
    checks.append({'prime':prime,'ports':vals,'old_output':a[OUT],'new_output':b[OUT]})
  check(canonical(ancestor)==before,'parent remains inert and unchanged')
  result={k:v for k,v in p.items()if k not in('source','source_sha256','ledger','certificate_ledger','control_interfaces')}
  result.update(source=new,source_sha256=sha(canonical(new)),ledger=dict(ledger,witnesses=67),certificate_ledger=certificate,control_interfaces=info['interfaces'])
  result['valid_recipe']=('Fixed E=3^e; C is dyadic, C>=64 and C>E; B=C*(x+height_slack), ordinary input x>0. Selected codes have maximum40, below B>=128.'if two else'Fixed positive program E=3^e from the inherited U21 compiler; literal radix B=64*(E+x+height_slack), ordinary input x>0. Selected codes have maximum40, below B>=192.')
  packets.append({'interface':'two_program'if two else'one_program','immediate_parent':stem,'packet':result,
                  'recipe':info,'exact_contract':proof,'degree_proof':deg,'signed_full_source_checks':checks})
 one=packets[0]['packet']['source'];two=packets[1]['packet']['source'];structural=[]
 for row in one:
  if row[0]=='height_83':continue
  if row[0]=='height_85':row=['height_85','+','input','height_slack']
  if row[0]=='radix_86':row=['radix_86','*','radix_program','height_85']
  structural.append(row)
 check(structural==two,'two independently rebuilt arrays differ only by actual height/radix interface')
 return {'status':'PASS_JOINT_U21_RECODING','source_sha256':sha(Path(__file__).read_bytes()),'dependencies':PINS,
         'packets':packets,'literal_program':program,'literal_primes':primes,'literal_edges':edges,
         'old_codes':OLD_CODES,'new_codes':CODES,'plan':{'weights':{str(k):v for k,v in WEIGHTS.items()},'increment_coefficient':4,'corrections':{str(k):v for k,v in CORRECTIONS.items()},'halt':14,'target_basis':BASIS},
         'chronology_diagnostics':chronology(edges),
         'interface_comparison':'The literal arrays differ only by deleting height_83 and changing the two height/radix definitions; no positive coordinate equivalence between interfaces is claimed.',
         'scope':'Two separately guarded complete sources, each with same supplied positive zero set as its own immediate parent. No cross-interface positive map, numerical minimum, exact degree, native tuple or below84 claim.'}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True)
 group=parser.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 a=parser.parse_args();result=build(a.root)
 if a.output:
  with a.output.open('x')as stream:stream.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:check(canonical(read(a.expect))==canonical(result),'exact type-sensitive receipt')
 print(result['status'],[p['packet']['ledger']for p in result['packets']])
if __name__=='__main__':main()
