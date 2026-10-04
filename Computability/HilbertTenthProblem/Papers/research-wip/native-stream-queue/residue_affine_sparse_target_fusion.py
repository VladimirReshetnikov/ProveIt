"""Fresh full-source target coefficient fusion; predecessors are inert bytes only."""
import argparse
import hashlib
import json
import random
from collections import Counter
from pathlib import Path

PINS = {
 'residue_affine_sparse_prime_recenter.py':'c5d8b2690f1e2a9b50aa063a95f81297ff388b276ab83ce487aa4cbaacc46798',
 'residue_affine_sparse_prime_recenter.json':'e35399b892850ace2bf860fd37f0e3e9f8af34dd8e516f66718547e0689fe26c',
 'residue_affine_sparse_prime_recenter.md':'78e81a12145ecf2b5b57fecdbef614cafa2a96ff0b86e488c4479546914c108c',
}
OUTPUT = 'norm_output'
GROUP = 'target_seven_group'
DELETE = {'joint_34','joint_46'}
GUARDS = [
 ['joint_34','*',6,'edge_29'],
 ['joint_46','+','joint_45','joint_34'],
 ['joint_35','*',7,'prime_selector_112'],
 ['joint_47','+','joint_46','joint_35'],
 ['joint_56','+','joint_55','selectors_70'],
 ['selectors_70','+','u21_grouped_J_7','edge_29'],
]
EDIT = {
 'joint_35':['joint_35','*',7,GROUP],
 'joint_47':['joint_47','+','joint_45','joint_35'],
 'joint_56':['joint_56','+','joint_55','u21_grouped_J_7'],
}
NEW = [GROUP,'+','prime_selector_112','edge_29']
EXCEPTIONS = ['joint_35']+[f'joint_{i}' for i in range(47,56)]

def need(condition, message):
 if not condition: raise ValueError(message)

def sha(data): return hashlib.sha256(data).hexdigest()
def canonical(value): return json.dumps(value,sort_keys=True,separators=(',',':')).encode()

def read(path):
 def pairs(items):
  result={}
  for k,v in items:
   need(k not in result,'duplicate JSON key');result[k]=v
  return result
 def bad(value): raise ValueError('noninteger JSON value '+value)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)

def table(rows):
 result={}
 for row in rows:
  need(type(row)is list and len(row)==4,'row shape')
  n,o,a,b=row
  need(type(n)is str and n not in result and o in ('+','-','*'),'SSA/opcode')
  need(type(a)in (int,str) and type(b)in (int,str),'operand types');result[n]=row
 return result

def closure(definitions, roots):
 live=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n in definitions and n not in live:
   live.add(n);todo.extend(definitions[n][2:])
 return live

def count(rows):
 c=Counter(row[1]for row in rows)
 return {'operations':len(rows),'multiplications':c['*'],'additions_subtractions':c['+']+c['-']}

def audit(rows, free):
 definitions=table(rows);seen=set(free);used=set()
 need(len(free)==len(seen),'unique supplied ports')
 for n,o,a,b in rows:
  need(n not in seen and all(type(v)is int or v in seen for v in (a,b)),'acyclic paid source')
  seen.add(n);used.update(v for v in(a,b)if type(v)is str)
 need(closure(definitions,[OUTPUT])==set(definitions),'all rows live')
 need(used-set(definitions)==set(free),'all and only supplied ports live')
 return count(rows)

def add(a,b,sign=1):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+sign*c
 return {m:c for m,c in r.items()if c}

def multiply(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   t=tuple(sorted(m+n));r[t]=r.get(t,0)+c*d
 return {m:c for m,c in r.items()if c}

def expansion(rows, target, cuts):
 definitions=table(rows);memo={n:{(n,):1}for n in cuts}
 def at(n):
  if type(n)is int:return {():n}if n else{}
  if n not in memo:
   need(n in definitions,'unbound polynomial port '+n)
   _,o,a,b=definitions[n];a,b=at(a),at(b)
   memo[n]=multiply(a,b)if o=='*'else add(a,b,1 if o=='+'else-1)
   need(len(memo[n])<3000,'bounded sparse expansion')
  return memo[n]
 return at(target)

def serial(p): return [[list(m),c]for m,c in sorted(p.items())]

def transform(old):
 d=table(old)
 for row in GUARDS:need(d[row[0]]==row,'literal guard '+row[0])
 consumers={n:[r[0]for r in old if n in r[2:]]for n in DELETE}
 need(consumers=={'joint_34':['joint_46'],'joint_46':['joint_47']},'private removed rows')
 need(GROUP not in d,'fresh group name')
 rows=[]
 for row in old:
  if row[0]in DELETE:continue
  if row[0]=='joint_35':rows.append(NEW)
  rows.append(EDIT.get(row[0],row))
 return rows,consumers

def exact_identity(old,new,free):
 # Exact integer affine vectors plus exact expression tuples. Digests are not
 # used to identify algebraic expressions. All boundary IDs arise from actual rows.
 interned={}
 def intern(key):
  if key not in interned:interned[key]=len(interned)
  return interned[key]
 def affine(poly):return intern(('affine',tuple(sorted(poly.items()))))
 def run(rows):
  polys={n:{n:1}for n in free};ids={n:affine(polys[n])for n in free}
  def value(n):
   if type(n)is int:
    p={'':n}if n else{};return affine(p),p
   return ids[n],polys[n]
  for n,o,a,b in rows:
   ia,pa=value(a);ib,pb=value(b);p=None
   if pa is not None and pb is not None:
    if o in('+','-'):p=add(pa,pb,1 if o=='+'else-1)
    elif not set(pa)-{''}:p={k:pa.get('',0)*v for k,v in pb.items()if pa.get('',0)*v}
    elif not set(pb)-{''}:p={k:pb.get('',0)*v for k,v in pa.items()if pb.get('',0)*v}
   polys[n]=p
   ids[n]=affine(p)if p is not None else intern((o,tuple(sorted((ia,ib)))if o in('+','*')else(ia,ib)))
  return ids
 a,b=run(old),run(new)
 need(a[OUTPUT]==b[OUTPUT],'complete polynomial identity')
 changed=sorted(n for n in a if n in b and a[n]!=b[n])
 need(changed==sorted(EXCEPTIONS),'exact retained-value exceptions')
 boundaries=['joint_24','joint_56','joint_61','joint_63','joint_64','sparse_all_units']+[f'norm_residual{i}'for i in range(6)]
 for n in boundaries:need(a[n]==b[n],'bound actual interface '+n)
 return {'method':'exact interned integer affine forms and expression tuples, no hash-as-identity assumption',
         'complete_output_equal':True,'equal_actual_boundaries':boundaries,
         'retained_value_exceptions':changed,'equal_retained_computed_values':sum(n in b and a[n]==b[n]for n in table(old)),
         'expression_nodes':len(interned)}

def degree(rows, free, two):
 def propagate(special=None):
  values={n:1 for n in free}
  for n,o,a,b in rows:
   a=values[a]if type(a)is str else 0;b=values[b]if type(b)is str else 0
   values[n]=a+b if o=='*'else max(a,b)
   if n=='native__R15'and special is not None:values[n]=special
  return values
 raw=propagate();X,a,c,G=['native__wn2','native__R12','native__R10a','native__gam']
 terms=[((X,X),1),((a,c,X),2),((G,X),2),((a,c,G),2),((G,G),1),((a,c,c),-4),((c,c),-3)]
 expected={tuple(sorted(m)):v for m,v in terms}
 need(expansion(rows,'native__R15',{X,a,c,G})==expected,'literal norm cancellation')
 weights={n:raw[n]for n in(X,a,c,G)}
 need(list(weights.values())==([312,379,68,380]if two else[308,374,67,375]),'actual degree boundary')
 norm=max(sum(weights[n]for n in m)for m in expected);guarded=propagate(norm)
 need((norm,guarded[OUTPUT],guarded['sparse_all_units'],guarded['norm_sum5'],raw[OUTPUT])==
      ((827,5160,5062,98,5227)if two else(816,5091,4993,98,5157)),'degree propagation')
 return {'upper_bound':guarded[OUTPUT],'native_norm_bound':norm,'native_product_bound':guarded['sparse_all_units'],
         'outer_SOS_bound':98,'naive_bound':raw[OUTPUT],'actual_cut_weights':weights,
         'exact_norm_expansion':serial(expected),'exact_degree_claimed':False}

def evaluate(rows, values, prime):
 values=dict(values)
 for n,o,a,b in rows:
  a=values[a]if type(a)is str else a;b=values[b]if type(b)is str else b
  values[n]=(a*b if o=='*'else a+b if o=='+'else a-b)%prime
 return values

def build(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'inert dependency '+name)
 parent=read(root/'residue_affine_sparse_prime_recenter.json');snapshot=canonical(parent)
 need(parent['source_sha256']==PINS['residue_affine_sparse_prime_recenter.py'],'parent helper binding')
 codes=parent['state_codes'];edges=parent['literal_edges']
 need(codes==[0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14],'literal codes')
 need(len(edges)==36 and len(set(codes))==23 and codes[0]==0 and min(codes[1:])==1 and max(codes)==40,'same valid code range')
 results=[]
 for two,item in enumerate(parent['packets']):
  need(item['interface']==('two_program'if two else'one_program'),'interface order')
  p=item['packet'];old=p['source'];free=p['parameters']+p['witnesses']
  need(sha(canonical(old))==p['source_sha256'],'literal parent array binding')
  need(len(free)==(70 if two else 69)and len(p['witnesses'])==67,'supplied domains')
  new,consumers=transform(old);od,nd=table(old),table(new)
  before=audit(old,free);after=audit(new,free)
  need(before==dict(operations=465 if two else 466,multiplications=171,additions_subtractions=294 if two else 295),'parent full ledger')
  need(after==dict(operations=464 if two else 465,multiplications=170,additions_subtractions=294 if two else 295),'successor full ledger')
  need(set(od)-set(nd)==DELETE and set(nd)-set(od)=={GROUP},'exact deletion/insertion census')
  need(all(nd[n]==od[n]for n in set(nd)&set(od)-set(EDIT)),'all other rows literal')
  base=closure(od,['sparse_all_units']+[f'norm_residual{i}'for i in(0,2,3,4,5)])
  need(len(base)==(388 if two else 389)and all(nd[n]==od[n]for n in base),'entire noncontrol base literal')
  for prefix,expected in [('native__',72),('norm_',20)]:
   a=[r for r in old if r[0].startswith(prefix)];b=[r for r in new if r[0].startswith(prefix)]
   need(a==b and len(a)==expected,'literal protected cone '+prefix)
  for r in p['literal_height_radix_rows']:need(nd[r[0]]==r,'actual height/radix')
  identity=exact_identity(old,new,free)
  hats={f'edge{i}_hat'for i in range(36)}
  for i in range(36):need(nd[f'edge_{i}']==[f'edge_{i}','-',f'edge{i}_hat',1],'actual edge hats')
  boundaries={}
  for n,indices in [('edge_29',[29]),('prime_selector_112',[5,8,9,14]),
                    ('selectors_70',list(range(36))),('u21_grouped_J_7',[i for i in range(36)if i!=29])]:
   want={():-len(indices),**{(f'edge{i}_hat',):1 for i in indices}}
   got=expansion(old,n,hats);need(got==want,'actual paid donor support '+n)
   boundaries[n]=serial(got)
  words={}
  for label,target,index in [('current','joint_24',0),('target','joint_61',1)]:
   a=expansion(old,target,hats);b=expansion(new,target,hats)
   coefficients=[codes[e[index]]for e in edges]
   want={():-sum(coefficients),**{(f'edge{i}_hat',):k for i,k in enumerate(coefficients)if k}}
   need(a==b==want,'entire actual-hat '+label+' vector');words[label]=serial(a)
  e={(f'edge29_hat',):1,():-1}
  differences={}
  for n in EXCEPTIONS:
   delta=add(expansion(new,n,hats),expansion(old,n,hats),-1)
   need(delta=={m:(7 if n=='joint_35'else 1)*c for m,c in e.items()},'exact intermediate discrepancy '+n)
   differences[n]=serial(delta)
  finalcuts={'sparse_all_units'}|{f'norm_residual{i}'for i in range(6)}
  final=expansion(new,OUTPUT,finalcuts)
  expected={():-1,('sparse_all_units',):1}
  for i in range(6):expected[tuple(sorted(('sparse_all_units',f'norm_residual{i}',f'norm_residual{i}')))]=1
  need(final==expected==expansion(old,OUTPUT,finalcuts),'full literal finalizer contraction')
  word_ledgers=[]
  for rows in(old,new):
   d=table(rows);current=closure(d,['joint_24'])-base;target=closure(d,['joint_61'])-base
   word_ledgers.append({'current':count([d[n]for n in current]),'target':count([d[n]for n in target]),
                        'union':count([d[n]for n in current|target]),'shared':sorted(current&target)})
  need(word_ledgers[1]['union']==dict(operations=58,multiplications=19,additions_subtractions=39),'live58 word union')
  need(word_ledgers[1]['shared']==['joint_12'],'paid shared scalar')
  certificate=count([r for r in new if not r[0].startswith('norm_')]);certificate.update(equations=7,witnesses=67)
  need(certificate==dict(operations=444 if two else 445,multiplications=163,additions_subtractions=281 if two else 282,equations=7,witnesses=67),'paid certificate ledger')
  bounds=degree(new,free,two);need(bounds['upper_bound']==p['polynomial_degree_upper_bound'],'inherited bound')
  modular=[];rng=random.Random(2026100407+two)
  for prime in(1000000007,1000000009):
   for _ in range(16):
    ports={n:rng.randrange(-43,44)for n in free};a,b=evaluate(old,ports,prime),evaluate(new,ports,prime)
    need(a[OUTPUT]==b[OUTPUT],'whole output modular diagnostic')
    for n in set(od)&set(nd)-set(EXCEPTIONS):need(a[n]==b[n],'retained value diagnostic')
    modular.append({'prime':prime,'ports':ports,'output':b[OUTPUT]})
  packet=dict(p);packet.update(source=new,source_sha256=sha(canonical(new)),ledger=dict(after,witnesses=67),certificate_ledger=certificate)
  results.append({'interface':item['interface'],'packet':packet,'old_ledger':before,'consumer_guard':consumers,
                  'base_rows_literal':len(base),'native_rows_literal':72,'finalizer_rows_literal':20,
                  'whole_source_identity':identity,'full_actual_hat_words':words,'formal_finalizer':serial(final),
                  'paid_donor_polynomials':boundaries,'exact_intermediate_differences':differences,
                  'old_new_word_ledgers':word_ledgers,'degree_proof':bounds,'signed_modular_checks':modular})
 need(canonical(parent)==snapshot,'parent in-memory data unchanged')
 one=results[0]['packet']['source'];two=results[1]['packet']['source'];mapped=[]
 for r in one:
  if r[0]=='height_83':continue
  if r[0]=='height_85':r=['height_85','+','input','height_slack']
  if r[0]=='radix_86':r=['radix_86','*','radix_program','height_85']
  mapped.append(r)
 need(mapped==two,'distinct full-interface relation preserved')
 return {'status':'PASS_EXACT_TARGET_FUSION','source_sha256':sha(Path(__file__).read_bytes()),'dependencies':PINS,
         'packets':results,'literal_edges':edges,'state_codes':codes,'literal_guards':GUARDS,
         'deleted_rows':sorted(DELETE),'changed_rows':EDIT,'new_row':NEW,
         'identity':'6E29+7A+J = 7(A+E29)+J7, with actual paid J=J7+E29',
         'scope':'Each full polynomial is identical to its own parent at every supplied value over every commutative ring; unchanged positive domains and fixed program recipes; no global arithmetic minimum or new compiler theorem.'}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True)
 group=parser.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 args=parser.parse_args();result=build(args.root)
 if args.output:
  with args.output.open('x')as stream:stream.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:need(canonical(read(args.expect))==canonical(result),'exact type-sensitive receipt equality')
 print(result['status'],[r['packet']['ledger']for r in result['packets']])

if __name__=='__main__':main()
