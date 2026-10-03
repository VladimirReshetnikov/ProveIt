"""Exact finite digit-permutation search in one paid C2 affine architecture.

All120 encodings use a=0, other digits1..5 and descending copy order.
This is not an optimum over other linear circuits or word encodings.
"""
import argparse
from copy import deepcopy
from functools import lru_cache
import hashlib
import random
import sys,json
from collections import Counter,defaultdict
from itertools import permutations
from pathlib import Path
import tseytin_zero_a388 as parent
RELATIONS=(('ac','ca'),('ad','da'),('bc','cb'),('bd','db'),('eca','ce'),('edb','de'),('cdca','cdcae'),('caaa','aaa'),('daaa','aaa'))
assert RELATIONS==parent.literal.RELATIONS
CANONICAL=parent.build()
oldnames={n for n,*_ in CANONICAL['source'] if n.startswith('linear') or n=='c2_shared_update_offset'}
oldkernel=[r for r in CANONICAL['source'] if r[0] in oldnames]
assert Counter(o for _,o,_,_ in oldkernel)=={'*':31,'+':44,'-':3}
assert len(oldkernel)==78

DEFAULT=dict(a=0,b=3,c=1,d=2,e=4,**{'#':5})

def validate_digits(d):
 assert isinstance(d,dict) and set(d)==set('abcde#')
 assert all(type(v)is int for v in d.values())
 assert d['a']==0 and sorted(d[c] for c in 'bcde#')==[1,2,3,4,5]


class Builder:
 def __init__(self):self.rows=[];self.serial=0
 def op(self,op,a,b,name=None):
  if name is None:name=f'permutation_scout_{self.serial}';self.serial+=1
  self.rows.append((name,op,a,b));return name
 def add(self,a,b,name=None):return self.op('+',a,b,name)
 def sub(self,a,b,name=None):return self.op('-',a,b,name)
 def times(self,n,a):return a if n==1 else self.op('*',n,a)
 def sum(self,values,name=None):
  assert values
  out=values[0]
  for v in values[1:-1]:out=self.add(out,v)
  if len(values)>1:out=self.add(out,values[-1],name)
  return out

def raw(word,d):
 out=0
 for c in word:out=8*out+d[c]
 return out

def plan(d):
 validate_digits(d)
 copies=tuple(sorted('abcde#',key=d.get,reverse=True))
 assert [d[c] for c in copies]==[5,4,3,2,1,0]
 tiles=tuple((c,c) for c in copies)+tuple(t for a,b in RELATIONS for t in ((a,b),(b,a)))
 maps=[(8**len(a),raw(a,d),8**len(b),raw(b,d)) for a,b in tiles]
 assert all(min(row)>0 or (row[1]==0 or row[3]==0) for row in maps)
 assert all(max(a+c,b+dd)<65536 for a,c,b,dd in maps)
 b=Builder();hat=lambda i:f'Shat{i}'
 pairs=[]
 for i in range(7):pairs.append(b.add(hat(6+2*i),hat(7+2*i),f'linear_group__{362+2*i}'))
 common=b.sum(['Shat0','selector_sum__4','selector_sum__5','selector_sum__6','selector_sum__7'])
 minima=[]
 for i,pair in enumerate(pairs):
  k=min(maps[6+2*i][1],maps[6+2*i][3]);assert k>0;minima.append(k)
  common=b.add(common,b.times(k,pair))
 assert all(min(maps[6+2*i][1],maps[6+2*i][3])==0 for i in (7,8))
 slope_differences={'U':[-56,448,4032,32704],'V':[-56,448,32704,4032]}
 totals=[sum(row[j] for row in maps) for j in (1,3)];assert totals[0]==totals[1]
 const=totals[0]+sum(slope_differences['U']);assert const>0
 common=b.sub(common,const,'c2_shared_update_offset')
 groups={};adjplans=[]
 for side,j,outname in [('U',1,'linear_constant__411'),('V',3,'linear_constant__430')]:
  current=b.sum([b.times(64,f'H_{side}')]+[b.times(k,f'Z{side}hat{i}') for i,k in enumerate(slope_differences[side])])
  g=defaultdict(list)
  for r in range(4):
   a,c=maps[6+2*r][1],maps[6+2*r][3];high=(6+2*r)+(a<c)
   if side=='V':high^=1
   g[abs(a-c)].append(hat(high))
  groups[side]=dict(g)
  for k,terms in sorted(g.items()):current=b.add(current,b.times(k,b.sum(terms)))
  # Compare direct two terms with both paid-sum decompositions. The exact
  # multiplication-by-one discount is included, as is the accumulation.
  c0=maps[14][1]-maps[14][3];c1=maps[16][1]-maps[16][3]
  assert c0>0 and c1>c0 and c1-c0==d['b']
  direct=(int(c0!=1)+int(c1!=1),2)
  grouped=(int(c1!=1)+int(c1-c0!=1),2)
  assert grouped<=direct
  pair='group_sum__221' if side=='U' else 'group_sum__228';first=hat(14 if side=='U' else 15)
  correction=b.sub(b.times(c1,pair),b.times(c1-c0,first))
  current=b.add(current,correction);adjplans.append(dict(direct=direct,grouped=grouped))
  for r in (6,7,8):
   a,c=maps[6+2*r][1],maps[6+2*r][3];high=6+2*r+(a<c)
   if side=='V':high^=1
   current=b.add(current,b.times(abs(a-c),hat(high)))
  b.add(common,current,outname)
 return dict(digits=d,copies=''.join(copies),tiles=tiles,maps=maps,rows=b.rows,minima=minima,commutation_groups=groups,adjacent=adjplans,constant=const)

# Exact symbolic linear coefficient executor. This is independent of both
# the parent evaluator and the generic affine compiler.
def add(a,b,sign=1):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def multiply(a,b):
 assert set(a)<=set([None]) or set(b)<=set([None])
 if set(a)<=set([None]):k=a.get(None,0);return {i:k*v for i,v in b.items() if k*v}
 return multiply(b,a)
def coefficients(rows):
 supplied=['H_U','H_V']+[f'Z{s}hat{i}' for s in 'UV' for i in range(4)]+[f'Shat{i}' for i in range(24)]
 env={n:{n:1} for n in supplied}
 for i in range(4,9):env[f'selector_sum__{i}']={f'Shat{j}':1 for j in range(i-2)}
 env['group_sum__221']={'Shat14':1,'Shat16':1};env['group_sum__228']={'Shat15':1,'Shat17':1}
 get=lambda n:env[n] if isinstance(n,str) else ({None:n} if n else {})
 pending=list(rows)
 while pending:
  nextrows=[];progress=False
  for n,o,a,b in pending:
   if isinstance(a,str) and a not in env or isinstance(b,str) and b not in env:nextrows.append((n,o,a,b));continue
   assert n not in env
   env[n]=multiply(get(a),get(b)) if o=='*' else add(get(a),get(b),1 if o=='+' else -1);progress=True
  assert progress
  pending=nextrows
 return env

# Topological emitter for complete sources; no parent sorting/closure helper.
def sortrows(rows,supplied):
 seen=set(supplied);pending=list(rows);result=[]
 assert len({r[0] for r in rows})==len(rows)
 while pending:
  rest=[];progress=False
  for row in pending:
   n,o,a,b=row
   if all(type(v)is int or v in seen for v in (a,b)):
    assert n not in seen;seen.add(n);result.append(row);progress=True
   else:rest.append(row)
  assert progress
  pending=rest
 return result

def live(rows,out):
 nodes={n:(a,b) for n,_,a,b in rows};active=set();todo=[out]
 while todo:
  n=todo.pop()
  if isinstance(n,str) and n in nodes and n not in active:active.add(n);todo.extend(nodes[n])
 assert active==nodes.keys()


def query_changes(d,old):
 validate_digits(d);rows={n:(o,a,b) for n,o,a,b in old['source']};h=parent.coefficients();den=parent.loader.DENOMINATOR;change={}
 for n,i in [('query_degree4',4),('query_degree3',3),('query_degree1',1),('query_numerator',0)]:
  value=8*d['b']*h[i]+(d['#']*den if i==0 else 0);assert value<0
  change[n]=('-',rows[n][1],-value)
 change['c2_terminal']=('+','c2_terminal_product',d['#']*512)
 return change


def program_parameter(S,digits=None):
 """Arithmetic recipe; universality requires the inherited valid primary S."""
 d=DEFAULT if digits is None else digits;validate_digits(d)
 assert isinstance(S,str) and set(S)<=set('cd')
 A=8*(parent.loader.DENOMINATOR*8**17*(8**len(S)+raw(S,d))+d['b']*parent.coefficients()[6])
 assert A>0
 return A


def rewrite(old,digits):
 validate_digits(digits);merge=old.get('merge_units')
 assert type(merge)is bool and old==parent.build(merge_units=merge),'complete canonical388 parent required'
 outside={a for n,_,x,y in old['source'] if n not in oldnames for a in (x,y) if a in oldnames}
 expected={f'linear_group__{n}' for n in (362,364,366,368,374)}|{'linear_constant__411','linear_constant__430'}
 assert outside==expected,'exact kernel boundary required'
 r=plan(digits);change=query_changes(digits,old)
 retained=[(n,*change.get(n,(o,a,b))) for n,o,a,b in old['source'] if n not in oldnames]
 assert not {n for n,*_ in r['rows']}&({n for n,*_ in retained}|set(old['parameters']+old['auxiliaries']))
 source=sortrows(retained+r['rows'],old['parameters']+old['auxiliaries'])
 keys=('parameters','auxiliaries','comparisons','ordinary_comparisons','unit_register','word_unit_register',
       'power_unit_register','word_factors','power_factors','merge_units','interfaces')
 packet=parent.scale.metadata(dict({k:deepcopy(old[k]) for k in keys},source=source,
     letter_codes=dict(digits),tiles=r['tiles'],copy_order=r['copies'],restricted_permutation=True,
     positive_integer_domain=True,identical_complete_polynomial_to388=digits==parent.CODES,
     identical_positive_zero_set_to388=digits==parent.CODES,
     program_recipe='For inherited valid literal S over c,d, A=8*(d*8^17*enc_codes(S)+code(b)*h6_zero_a388); d=8^64-1.',
     projection='Same universal accepted positive inputs on the separately recompiled valid program slices; no supplied-coordinate bijection across encodings.',
     architecture='Paid copy prefixes; shared per-pair minima; grouped equal commutation differences; direct or paid adjacent selector-pair decomposition; omit multiplication by1.',
     kernel_rows=r['rows'],common_pair_minima=r['minima'],commutation_groups=r['commutation_groups'],
     shared_hat_offset=r['constant']))
 parent.scale.checked_source(source,packet['parameters'],packet['auxiliaries'])
 assert packet['witnesses']==62
 return packet


def build(digits=None,*,merge_units=True):
 assert type(merge_units)is bool
 return rewrite(parent.build(merge_units=merge_units),DEFAULT if digits is None else digits)


def checked_packet(packet):
 assert packet==build(packet['letter_codes'],merge_units=packet['merge_units']),'complete canonical restricted-architecture packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
 if packet is None:packet=build()
 checked_packet(packet);assert type(sum_of_squares)is bool
 return parent.literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
 checked_packet(packet)
 return parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def ledger(packet=None,*,sum_of_squares=False):
 if packet is None:packet=build()
 rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares);cc=Counter(o for _,o,_,_ in rows)
 degrees=degree_dictionary(packet);deg=lambda v:degrees[v] if isinstance(v,str) else 0
 for n,o,a,b in rows:
  if n not in degrees:degrees[n]=deg(a)+deg(b) if o=='*' else max(deg(a),deg(b))
 live(rows,out)
 return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
     polynomial=dict(operations=len(rows),multiplications=cc['*'],additions_subtractions=cc['+']+cc['-'],
                     degree_upper_bound=degrees[out],exact_degree_claimed=False))


def execute(rows,values,overrides=None):
 e=dict(values);overrides={} if overrides is None else overrides
 at=lambda v:e[v] if isinstance(v,str) else v
 for n,o,a,b in rows:
  assert n not in e
  e[n]=overrides[n](e) if n in overrides else at(a)*at(b) if o=='*' else at(a)+at(b) if o=='+' else at(a)-at(b)
 return e


def modified_parent(old,d,values,sos=False):
 """Independent complete evaluator with only boundary/constant overrides."""
 r=plan(d);change=query_changes(d,old);overrides={}
 for name,(o,a,b) in change.items():
  overrides[name]=lambda e,o=o,a=a,b=b:(e[a] if isinstance(a,str) else a)+(b if o=='+' else -b)
 for side,j,out in [('U',1,'linear_constant__411'),('V',3,'linear_constant__430')]:
  differences=[-56,448,4032,32704] if side=='U' else [-56,448,32704,4032]
  overrides[out]=lambda e,side=side,j=j,differences=differences:64*e[f'H_{side}']+sum(k*(e[f'Z{side}hat{i}']-1) for i,k in enumerate(differences))+sum(row[j]*(e[f'Shat{i}']-1) for i,row in enumerate(r['maps']))
 rows,out=parent.polynomial_source(old,sum_of_squares=sos)
 return execute(rows,values,overrides),out


def search_audit():
 records=[];counts=Counter();den=parent.loader.DENOMINATOR;h=parent.coefficients()
 neg=parent.fusion.sign_filter();rng=random.Random(120387388)
 for rest in permutations(range(1,6)):
  d=dict(a=0,**dict(zip('bcde#',rest)));r=plan(d);env=coefficients(r['rows'])
  for side,j,name in [('U',1,'linear_constant__411'),('V',3,'linear_constant__430')]:
   target={f'H_{side}':64,None:-r['constant']};diffs=[-56,448,4032,32704] if side=='U' else [-56,448,32704,4032]
   target.update({f'Z{side}hat{i}':v for i,v in enumerate(diffs)})
   target.update({f'Shat{i}':row[j] for i,row in enumerate(r['maps']) if row[j]})
   assert env[name]==target;counts['exact_symbolic_affine_update_identities']+=1
  G=len(r['commutation_groups']['U']);assert G==len(r['commutation_groups']['V'])
  t=int(d['c']==1 or d['d']==1);adj=2 if d['b']==1 else 4
  assert len(r['rows'])==70+2*G+adj-t
  kc=Counter(o for _,o,_,_ in r['rows'])
  assert kc['*']==23+2*G+adj-t and kc['+']+kc['-']==47
  assert G>=2 and (d['b']!=1 or (G>=3 and t==0))
  forms=[]
  for merge in (False,True):
   packet=build(d,merge_units=merge);old=parent.build(merge_units=merge)
   for sos in (False,True):
    rec=ledger(packet,sum_of_squares=sos)
    assert rec['polynomial']['operations']==380+2*G+adj-t+2*(not merge)
    assert rec['polynomial']['multiplications']==172+2*G+adj-t
    assert rec['polynomial']['additions_subtractions']==208+2*(not merge)
    expected=parent.degree_bound(old,sum_of_squares=sos)['degree_upper_bound']
    assert rec['polynomial']['degree_upper_bound']==expected
    rows,out=polynomial_source(packet,sum_of_squares=sos)
    for case in range(4):
     signed=case>=2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
     values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
     e=execute(rows,values);other,target=modified_parent(old,d,values,sos)
     assert e[out]==other[target]
     assert all(e[n]==other[n] for n,*_ in packet['source'] if n not in {n for n,*_ in r['rows']})
     counts['complete_modified_parent_outputs']+=1;counts['signed_outputs']+=signed
    forms.append(dict(merge_units=merge,sum_of_squares=sos,**rec));counts['complete_ledgers_and_degree_bounds']+=1
  for S in ('','c','d','cdcd','ddccc'):
   A=program_parameter(S,d)
   for x in (1,2,3):
    query=parent.loader.query_word(S,x);I=8**(len(query)+1)+raw(query+'#',d);Q=8**(32*x)
    assert den*I==A*Q**6+sum(8*d['b']*h[i]*Q**i for i in (0,1,3,4))+d['#']*den
    assert max(map(len,bin(I)[2:].split('1')))<=10
    counts['literal_query_height_checks']+=1
  for case,original in zip(neg['cases'],neg['parent_exact_certificate']['cases']):
   R=case['numerator_residue'];Q=original['Q_residue'];assert 0<d['b']*R<den
   actual=(sum(8*d['b']*h[i]*pow(Q,i,den) for i in (0,1,3,4,6))+d['#']*den)%den
   assert actual==d['b']*R;counts['wrong_power_residue_checks']+=1
  records.append(dict(digits=d,copies=r['copies'],operations=380+2*G+adj-t,multiplications=172+2*G+adj-t,
      additions_subtractions=208,distinct_commutation_magnitudes=G,unit_minimum_discount=t,adjacent_multiplications=adj,
      common_pair_minima=r['minima'],shared_hat_offset=r['constant'],maps=r['maps'],forms=forms))
 distribution=dict(sorted(Counter(r['operations'] for r in records).items()));winners=[r['digits'] for r in records if r['operations']==387]
 assert distribution=={387:16,388:16,389:24,390:36,391:8,392:20} and DEFAULT in winners
 return dict(minimum=387,distribution=distribution,minimizers=winners,records=records,audits=dict(counts))


def reference_audit():
 """Compare the same explicit winning encoding, without assuming a tree identity."""
 import tseytin_permuted_digits387 as reference
 totals=Counter();rng=random.Random(387120)
 assert reference.CODES==DEFAULT
 for merge in (False,True):
  p=build(merge_units=merge);q=reference.build(merge_units=merge)
  for sos in (False,True):
   rows,out=polynomial_source(p,sum_of_squares=sos);other,target=reference.polynomial_source(q,sum_of_squares=sos)
   for case in range(64):
    signed=case>=32;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
    values={n:draw() for n in p['parameters']+p['auxiliaries']}
    assert execute(rows,values)[out]==execute(other,values)[target]
    totals['complete_reference387_outputs']+=1;totals['signed_outputs']+=signed
 return dict(totals,scope='Same explicit encoding/program recipe. Both kernels equal the literal map linear forms; different product/addition trees are executed independently.')


def guards():
 rejected=0
 def reject(call):
  nonlocal rejected
  try:call()
  except (AssertionError,KeyError,TypeError):rejected+=1
  else:raise AssertionError('malformed caller accepted')
 for d in [dict(DEFAULT,a=1),dict(DEFAULT,b=1),dict(DEFAULT,c=True),dict(DEFAULT,c=1.0),{},dict(DEFAULT,z=6)]:reject(lambda d=d:build(d))
 old=parent.build()
 for key,value in [('source',old['source'][:-1]),('auxiliaries',old['auxiliaries'][:-1]),('letter_codes',{}),('program_recipe','arbitrary')]:
  reject(lambda key=key,value=value:rewrite(dict(old,**{key:value}),DEFAULT))
 p=build()
 for key,value in [('source',p['source'][:-1]),('letter_codes',parent.CODES),('tiles',()),('program_recipe','unrestricted'),('comparisons',[]),('kernel_rows',[])]:
  for api in (polynomial_source,degree_dictionary):reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
 return rejected


def verify():
 result=search_audit();emitted=[]
 for merge in (False,True):
  for sos in (False,True):
   p=build(merge_units=merge);rows,out=polynomial_source(p,sum_of_squares=sos)
   emitted.append(dict(merge_units=merge,sum_of_squares=sos,**ledger(p,sum_of_squares=sos),source=rows,output=out,
       parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
       source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()))
 return dict(status='PASS_TSEYTIN_ZERO_A_PERMUTATION_SEARCH',search=result,reference387=reference_audit(),
     emitted_default_sources=emitted,rejected_callers=guards(),
     scope='Exact120-case restricted affine architecture only; all digits/program words recompiled. No optimum over arbitrary circuits, encodings, radices or substrates. Universality is inherited only on valid program recipes.')


if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(path.read_text())==result,'receipt mismatch'
 print(result['status']);print(result['search']['distribution']);print(result['search']['audits'])
