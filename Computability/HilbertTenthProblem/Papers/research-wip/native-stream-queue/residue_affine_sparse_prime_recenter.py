"""Fresh exact prime-selector recentering of both complete U21 arrays.
All predecessor files are read only as authenticated inert bytes or JSON.
"""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={
 'residue_affine_sparse_joint_recoding.py':'386f00228dd250a1c582a3bf93724e9732db71cdd8d4fea6828d0b78d06fe443',
 'residue_affine_sparse_joint_recoding.json':'a3b00883d84e7c8e9a6aea04ec3e54776fe927f7193f60a04050246f32039284',
 'residue_affine_sparse_joint_recoding.md':'16d4a9e60343eb4f8f4ee78e8d60e7aeb2ee73b8d045241dd4951e124cf7b404'}
OUT='norm_output'
NEW='recentered_current_prefix'
GUARDS=[['joint_8','*',17,'prime_selector_113'],
 ['joint_1','+','edge_14','control_codes__duplicate_state_8'],
 ['joint_2','+','joint_1','edge_15'],
 ['joint_21','+','joint_20','joint_2'],
 ['joint_22','+','joint_21','joint_11']]
DELETE={'joint_1','joint_2'}
EDIT={'joint_8':['joint_8','*',18,'prime_selector_113'],
      'joint_21':['joint_21','+','joint_20','control_codes__duplicate_state_8'],
      'joint_22':['joint_22','+',NEW,'joint_11']}
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


def transform(old):
 defs=table(old)
 for row in GUARDS:check(defs[row[0]]==row,'literal edit guard '+row[0])
 consumers={n:[r[0]for r in old if n in r[2:]]for n in('joint_1','joint_2','joint_21')}
 check(consumers=={'joint_1':['joint_2'],'joint_2':['joint_21'],'joint_21':['joint_22']},'private group and prefix consumers')
 check(NEW not in defs,'fresh SSA name')
 rows=[]
 for row in old:
  if row[0]in DELETE:continue
  rows.append(EDIT.get(row[0],row))
  if row[0]=='joint_21':rows.append([NEW,'-','joint_21','prime_selector_111'])
 return rows,consumers

def exact_dag_identity(old,new,free):
 # Exact interned expression IDs, never digest equality. Affine values are
 # normalized over every actual supplied port, including the constant term.
 dictionary={}
 def intern(key):
  if key not in dictionary:dictionary[key]=len(dictionary)
  return dictionary[key]
 def affine(p):return intern(('affine',tuple(sorted(p.items()))))
 def run(rows):
  ids={n:affine({n:1})for n in free};polys={n:{n:1}for n in free}
  def val(x):return (affine({'':x}if x else{}),{'':x}if x else{})if type(x)is int else(ids[x],polys[x])
  for n,o,a,b in rows:
   ia,pa=val(a);ib,pb=val(b);p=None
   if pa is not None and pb is not None:
    if o in('+','-'):p=add(pa,pb,1 if o=='+'else-1)
    elif not set(pa)-{''}:p={k:pa.get('',0)*v for k,v in pb.items()if pa.get('',0)*v}
    elif not set(pb)-{''}:p={k:pb.get('',0)*v for k,v in pa.items()if pb.get('',0)*v}
   polys[n]=p
   ids[n]=affine(p)if p is not None else intern((o,tuple(sorted((ia,ib)))if o in('+','*')else(ia,ib)))
  return ids,polys
 a,ap=run(old);b,bp=run(new)
 check(a[OUT]==b[OUT],'exact entire source identity')
 affected=sorted(n for n in a if n in b and a[n]!=b[n])
 check(affected==sorted(['joint_8','joint_18','joint_19','joint_20','joint_21']),'exact retained-value exception list')
 check(a['joint_21']==b[NEW],'restored actual current prefix')
 for n in ['joint_24','joint_61','norm_residual1','sparse_all_units']+[f'norm_residual{i}'for i in range(6)]:
  check(a[n]==b[n],'actual boundary equality '+n)
 return {'method':'exact structural interning with affine normalization at actual supplied ports; no hashes substitute for expressions',
         'all_output_identical':True,'retained_value_exceptions':affected,'old_prefix_equals_new':NEW,
         'identical_retained_computed_values':sum(n in b and a[n]==b[n]for n in table(old)),
         'distinct_exact_expression_nodes':len(dictionary),
         'old_current_affine':sorted(ap['joint_24'].items()),'new_current_affine':sorted(bp['joint_24'].items()),
         'old_target_affine':sorted(ap['joint_61'].items()),'new_target_affine':sorted(bp['joint_61'].items())}

def build(root):
 for n,pin in PINS.items():check(sha((root/n).read_bytes())==pin,'dependency '+n)
 parent=read(root/'residue_affine_sparse_joint_recoding.json');saved=canonical(parent)
 check(parent['source_sha256']==PINS['residue_affine_sparse_joint_recoding.py'],'parent helper binding')
 check(parent['new_codes']==[0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14],'same literal code list')
 check(len(set(parent['new_codes']))==23 and max(parent['new_codes'])==40,'unchanged injective codes')
 check(len(parent['literal_edges'])==36 and len(parent['literal_program'])==21,'literal controller size')
 packets=[]
 for two,item in enumerate(parent['packets']):
  check(item['interface']==('two_program'if two else'one_program'),'interface order')
  p=item['packet'];old=p['source'];check(p['source_sha256']==sha(canonical(old)),'full old source binding')
  free=p['parameters']+p['witnesses'];check(len(free)==(70 if two else 69)and len(p['witnesses'])==67,'exact supplied counts')
  new,consumers=transform(old);od,nd=table(old),table(new)
  oldledger=audit(old,free);ledger=audit(new,free)
  check(oldledger==dict(operations=466 if two else 467,multiplications=171,additions_subtractions=295 if two else 296),'parent ledger')
  check(ledger==dict(operations=465 if two else 466,multiplications=171,additions_subtractions=294 if two else 295),'new ledger')
  check(len(set(od)-set(nd))==2 and set(nd)-set(od)=={NEW},'two deletions and one producer')
  check(all(nd[n]==od[n]for n in set(od)&set(nd)-set(EDIT)),'all other retained rows literal')
  base=closure(od,['sparse_all_units']+[f'norm_residual{i}'for i in(0,2,3,4,5)])
  check(len(base)==(388 if two else 389)and all(nd[n]==od[n]for n in base),'entire noncontrol base literal')
  check([r for r in new if r[0].startswith('native__')]==[r for r in old if r[0].startswith('native__')],'all72 native rows literal')
  check([r for r in new if r[0].startswith('norm_')]==[r for r in old if r[0].startswith('norm_')],'all20 finalizer rows literal')
  for r in p['literal_height_radix_rows']:check(nd[r[0]]==r,'height/radix unchanged')
  hats={f'edge{i}_hat'for i in range(36)};edges={f'edge_{i}'for i in range(36)}
  for i in range(36):check(nd[f'edge_{i}']==[f'edge_{i}','-',f'edge{i}_hat',1],'supplied selector hats')
  def selector(ids):return {(f'edge_{i}',):1 for i in ids}
  gp=expand(old,'prime_selector_113',edges);aa=expand(old,'prime_selector_111',edges);dd=selector([14,15]);d14=expand(old,'control_codes__duplicate_state_8',edges)
  check(gp==selector([5,8,9,14,15])and aa==selector([5,8,9])and d14==selector([24,25]),'literal donor support')
  check(gp==add(aa,dd),'G17=A3+D9')
  # Actual current/target words, fully expanded through all36 supplied hats.
  words={}
  for label,target in [('current','joint_24'),('target','joint_61')]:
   lhs=expand(old,target,hats);rhs=expand(new,target,hats);check(lhs==rhs,'entire '+label+' word identity')
   end=0 if label=='current'else 1;coeffs=[parent['new_codes'][e[end]]for e in parent['literal_edges']]
   want={():-sum(coeffs),**{(f'edge{i}_hat',):c for i,c in enumerate(coeffs)if c}}
   check(lhs==want,'actual edge-label vector '+label);words[label]=serial(lhs)
  finalcuts={'sparse_all_units'}|{f'norm_residual{i}'for i in range(6)}
  finals=expand(old,OUT,finalcuts);check(finals==expand(new,OUT,finalcuts),'entire finalizer contraction')
  want={():-1,('sparse_all_units',):1}
  for i in range(6):want[tuple(sorted(('sparse_all_units',f'norm_residual{i}',f'norm_residual{i}')))]=1
  check(finals==want,'actual U*(1+sum squares)-1')
  identity=exact_dag_identity(old,new,free)
  word_ledgers=[]
  for rows in(old,new):
   defs=table(rows);current=closure(defs,['joint_24'])-base;target=closure(defs,['joint_61'])-base
   def count(names):
    counts=Counter(defs[n][1]for n in names)
    return dict(operations=len(names),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'])
   word_ledgers.append({'current':count(current),'target':count(target),'union':count(current|target),'shared':sorted(current&target)})
  check(word_ledgers[0]['union']==dict(operations=60,multiplications=20,additions_subtractions=40),'old60 word union')
  check(word_ledgers[1]['union']==dict(operations=59,multiplications=20,additions_subtractions=39),'new59 word union')
  check(word_ledgers[1]['shared']==['joint_12'],'unchanged single shared coefficient product')
  cc=Counter(r[1]for r in new if not r[0].startswith('norm_'))
  cert=dict(operations=sum(cc.values()),multiplications=cc['*'],additions_subtractions=cc['+']+cc['-'],equations=7,witnesses=67)
  check(cert==dict(operations=445 if two else 446,multiplications=164,additions_subtractions=281 if two else 282,equations=7,witnesses=67),'complete certificate')
  d=degree(new,two);check(d['polynomial_degree_upper_bound']==p['polynomial_degree_upper_bound'],'inherited guarded degree')
  checks=[];rng=random.Random(2026100602+two)
  for prime in(1000000007,1000000009):
   for _ in range(16):
    ports={n:rng.randrange(-41,42)for n in free};a,b=evaluate(old,ports,prime),evaluate(new,ports,prime)
    check(a[OUT]==b[OUT],'signed whole source equality')
    check(a['joint_21']==b[NEW],'signed restored prefix')
    for n in set(od)&set(nd)-set(identity['retained_value_exceptions']):check(a[n]==b[n],'signed retained value')
    checks.append({'prime':prime,'ports':ports,'output':b[OUT]})
  result=dict(p);result.update(source=new,source_sha256=sha(canonical(new)),ledger=dict(ledger,witnesses=67),certificate_ledger=cert)
  packets.append({'interface':item['interface'],'packet':result,'literal_consumer_guard':consumers,
    'base_rows_literal':len(base),'native_rows_literal':72,'finalizer_rows_literal':20,
    'old_new_word_ledgers':word_ledgers,
    'whole_source_identity':identity,'full_actual_hat_words':words,'formal_finalizer':serial(finals),
    'donor_identity':{'G17':serial(gp),'A3':serial(aa),'D9':serial(dd),'D14':serial(d14)},
    'degree_proof':d,'signed_whole_source_checks':checks})
 check(canonical(parent)==saved,'inert parent unchanged')
 one=packets[0]['packet']['source'];two=packets[1]['packet']['source'];mapped=[]
 for row in one:
  if row[0]=='height_83':continue
  if row[0]=='height_85':row=['height_85','+','input','height_slack']
  if row[0]=='radix_86':row=['radix_86','*','radix_program','height_85']
  mapped.append(row)
 check(mapped==two,'same edit at two distinct actual interfaces')
 return {'status':'PASS_EXACT_PRIME_RECENTER','source_sha256':sha(Path(__file__).read_bytes()),'dependencies':PINS,
   'packets':packets,'new_producer':[NEW,'-','joint_21','prime_selector_111'],'deleted_rows':sorted(DELETE),'changed_rows':EDIT,
   'literal_edges':parent['literal_edges'],'state_codes':parent['new_codes'],
   'identity':'17*G17+(D9+D14)=18*G17+D14-A3, because G17=A3+D9; complete output unchanged over every commutative ring',
   'scope':'Same entire polynomial as each own parent; same fixed program recipes, supplied coordinates and ordinary-input meanings; no relation between distinct interfaces and no global minimality claim'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 result=build(a.root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:check(canonical(read(a.expect))==canonical(result),'exact receipt equality')
 print(result['status'],[p['packet']['ledger']for p in result['packets']])
if __name__=='__main__':main()
