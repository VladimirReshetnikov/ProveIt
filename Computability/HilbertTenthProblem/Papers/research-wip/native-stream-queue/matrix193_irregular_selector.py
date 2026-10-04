#!/usr/bin/env python3
"""Complete real-safe 96-node matrix lookup with compact fixed-numeral recipes."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

PINS={
 'matrix193_newton_selector.py':'a8437280c24b844f7cd0c5193ba9421a5be6e93901027023440709d7c74c3eb0',
 'matrix193_newton_selector.json':'21c47a877d2b36a435c3ffd7dbdb46a21a6c96f11c91d60637743ef20f3fbeff',
 'matrix193_newton_selector.md':'b5cd29a950c1e380969bb3a7cfe924b78a360e7ab2f61fff82151dc627de581e',
 'matrix193_lookup_schedule_scout.py':'5913b37641696e216cfb05fb9bd39a27ed72d2480be526df5bba628c6a7c19ce',
 'matrix193_lookup_schedule_scout.json':'c8205b9b193936f5685d3cb77a068ad5eb5e4b92136c78eb40187198b56e3da2',
 'matrix193_lookup_schedule_scout.md':'cc96b4a27da6d846fb257e7d603a662f27d5423266234e2a92f98b6a06d571f3',
}
STATE=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
COLS=['K0','K1','K2','K3','G0','G1','G2','G3']


def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def load(b):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(s):raise ValueError('noninteger JSON '+s)
 return json.loads(b,object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def integer_metadata(v):
 # Canonical exact integer encoding: ASCII sign followed by big-endian magnitude.
 b=(b'-' if v<0 else b'+')+abs(v).to_bytes((abs(v).bit_length()+7)//8,'big')
 return {'sign':(v>0)-(v<0),'magnitude_bits':abs(v).bit_length(),'signed_magnitude_sha256':sha(b)}


def compile_numerals(table):
 first=table[0]['G'][0]
 stride=math.gcd(*(r['G'][0]-first for r in table))
 need(stride==5,'node stride5')
 nodes=[(r['G'][0]-first)//stride for r in table]
 need(nodes[0]==0 and len(set(nodes))==96,'distinct integer nodes')
 denominators=[math.prod(nodes[i]-nodes[j] for j in range(96) if j!=i) for i in range(96)]
 scale=math.lcm(*denominators)
 need(scale>0 and all(scale%v==0 for v in denominators),'positive integral common scale')
 constants={'C:D':scale};coefs={};bindings={};division_checks=0
 for col in COLS:
  values=[scale*r[col[0]][int(col[1])] for r in table];coefficients=[values[0]]
  for j in range(1,96):
   next_values=[]
   for i in range(96-j):
    q,rem=divmod(values[i+1]-values[i],nodes[i+j]-nodes[i])
    need(rem==0,'exact integer divided difference');next_values.append(q);division_checks+=1
   values=next_values;coefficients.append(values[0])
  coefs[col]=coefficients;bindings[col]=[]
  for j,c in enumerate(coefficients):
   name='C:'+col+':'+str(j)
   if c:constants[name]=c;bindings[col].append(name)
   else:bindings[col].append(None)
 need(coefs['G0']==[scale*first,scale*5]+[0]*94,'linear selected column')
 zeros={col:[j for j,c in enumerate(cs) if j and not c] for col,cs in coefs.items()}
 need(zeros=={col:([1,2,3] if col[0]=='K' else list(range(2,96)) if col=='G0' else []) for col in COLS},'exact106 vanishing coefficients')
 # Independent closed divided-difference formula at selected orders.
 formula_checks=0
 for col in COLS:
  v=[r[col[0]][int(col[1])] for r in table]
  for j in [0,1,2,3,4,16,48,95]:
   expected=0
   for i in range(j+1):
    divisor=math.prod(nodes[i]-nodes[k] for k in range(j+1) if k!=i)
    q,rem=divmod(scale,divisor);need(rem==0,'Lagrange subset denominator divides scale')
    expected+=v[i]*q
   need(expected==coefs[col][j],'closed coefficient formula');formula_checks+=1
 # Independent nested evaluation of the exact fixed coefficients at all nodes.
 node_checks=0
 for col in COLS:
  cc=coefs[col]
  for i,z in enumerate(nodes):
   value=cc[-1]
   for j in range(94,-1,-1):value=value*(z-nodes[j])+cc[j]
   need(value==scale*table[i][col[0]][int(col[1])],'all768 exact interpolation values');node_checks+=1
 metadata={name:integer_metadata(v) for name,v in constants.items()}
 recipe={
  'scheme':'integer_scaled_Newton_fixed_numerals_v1',
  'inputs':'Only the pinned finite transition table and its saved order; no variable or witness input.',
  'nodes':nodes,'node_definition':{'column':'G0','first_value':first,'difference_gcd':stride},
  'scale_recipe':'D = lcm_i abs(product_(k != i)(nodes[i]-nodes[k])); all 96 nodes are used.',
  'coefficient_recipe':'C[col,j] = sum_(i=0)^j table[i][col] * (D / product_(0<=k<=j,k!=i)(nodes[i]-nodes[k])). Every displayed quotient is an exact fixed-integer quotient.',
  'integer_compiler_recurrence':'b[0,i]=D*table[i][col]; b[j,i]=(b[j-1,i+1]-b[j-1,i])/(nodes[i+j]-nodes[i]); C[col,j]=b[j,0]. Every division is checked for zero remainder before source evaluation.',
  'coefficient_bindings':bindings,'fixed_numeral_metadata':metadata,
  'metadata_encoding':'SHA256 of ASCII + or - followed by unsigned big-endian magnitude; zero has empty magnitude.',
  'zero_nonconstant_coefficients':zeros,
  'common_scale_bits':scale.bit_length(),
  'maximum_coefficient_bits':max(abs(c).bit_length() for cs in coefs.values() for c in cs),
  'maximum_node_bits':max(abs(z).bit_length() for z in nodes),
  'constant_leaf_convention':'Each recipe output is one fixed signed integer leaf, as in the parent fixed-numeral model. Fixed-integer compilation divisions are not variable operations. Every nonconstant source use is paid.',
  'checks':{'integer_recurrence_divisions':division_checks,'independent_closed_formula_coefficients':formula_checks,'exact_node_column_values':node_checks},
 }
 return nodes,constants,coefs,recipe


class Source:
 def __init__(self):self.rows=[]
 def op(self,op,a,b):
  name='g'+str(len(self.rows));self.rows.append([name,op,a,b]);return name
 def sum(self,terms):
  value=terms[0]
  for term in terms[1:]:value=self.op('+',value,term)
  return value


def build(nodes,constants,coefs,recipe):
 e=Source();prefixes=[1,'selector'];shifts=['selector']
 for j in range(1,96):
  shifts.append(e.op('-','selector',nodes[j]));prefixes.append(e.op('*',prefixes[-1],shifts[j]))
 lookup={}
 for col in COLS:
  cc=coefs[col];need(cc[0]!=0,'nonzero constant coefficient')
  value=recipe['coefficient_bindings'][col][0]
  for j in range(1,96):
   if not cc[j]:continue
   need(abs(cc[j])!=1,'declared multiplied coefficient is not a unit')
   term=e.op('*',recipe['coefficient_bindings'][col][j],prefixes[j]);value=e.op('+',value,term)
  lookup[col]=value
 lookup_end=len(e.rows);residuals=[]
 for off,kind in [(0,'K'),(2,'G')]:
  for j in [0,1]:
   left=e.op('*',STATE[off],lookup[kind+str(j)])
   right=e.op('*',STATE[off+1],lookup[kind+str(j+2)])
   pred=e.op('+',left,right);scaled=e.op('*','C:D',STATE[4+off+j])
   residuals.append(e.op('-',scaled,pred))
 selector_square=e.op('*',prefixes[96],prefixes[96])
 output=e.sum([selector_square]+[e.op('*',v,v) for v in residuals])
 return {'ports':STATE+['selector'],'instructions':e.rows,'output':output,'lookup_end':lookup_end,
  'lookup_wires':lookup,'basis_wires':prefixes,'selector_polynomial':prefixes[96],
  'selector_square':selector_square,'residual_wires':residuals,'scale_binding':'C:D',
  'domain':'signed real or integer ports; selector existential','extra_selector_witnesses':1,'exact_degree':192}


def append_countdown(p,parent):
 ps=parent['variants']['real_synchronized'];pc=parent['variants']['real_countdown']
 rows=[row[:] for row in p['instructions']];rename={ps['output']:p['output']}
 for old,op,a,b in pc['instructions'][len(ps['instructions']):]:
  name='g'+str(len(rows));rows.append([name,op,rename.get(a,a),rename.get(b,b)]);rename[old]=name
 need(len(rows)-len(p['instructions'])==26,'complete inherited26-row suffix')
 return {'ports':STATE+['selector','n','next_n'],'instructions':rows,'output':rename[pc['output']],
  'parent_tile_output':p['output'],'loader_factor':rename[pc['loader_factor']],
  'tile_factor':rename[pc['tile_factor']],'domain':p['domain'],'extra_selector_witnesses':1,'exact_degree':194}


def ledger(p,constants):
 known=set(p['ports'])|set(constants);degree={n:1 for n in p['ports']};degree.update({n:0 for n in constants});producers={}
 for n,op,a,b in p['instructions']:
  need(n not in known and op in ['+','-','*'],'source row')
  need(all(type(v)is int or type(v)is str and v in known for v in [a,b]),'source closure')
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b]
  degree[n]=da+db if op=='*' else max(da,db);known.add(n);producers[n]=(a,b)
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(producers.get(n,()))
 need(set(producers)|set(p['ports'])==live-set(constants),'all source rows and supplied ports live')
 need(set(constants)<=live,'every declared fixed numeral used')
 need(degree[p['output']]==p['exact_degree'],'formal degree upper bound')
 m=sum(row[1]=='*' for row in p['instructions'])
 return {'M':m,'A':len(p['instructions'])-m,'total':len(p['instructions']),
  'all_rows_ports_and_fixed_numerals_live':True,'fixed_numeral_bindings':len(constants)}


def run_rows(rows,values,op=None):
 env=dict(values)
 for name,kind,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  env[name]=op(kind,a,b) if op else a*b if kind=='*' else a+b if kind=='+' else a-b
 return env


class Ring:
 def __init__(self,names):self.names=names;self.zero=(0,)*len(names)
 def c(self,v):return {self.zero:v} if v else {}
 def v(self,name):
  e=list(self.zero);e[self.names.index(name)]=1;return {tuple(e):1}
 def op(self,kind,a,b):
  if type(a)is int:a=self.c(a)
  if type(b)is int:b=self.c(b)
  out={}
  if kind=='*':
   for e,x in a.items():
    for f,y in b.items():
     g=tuple(u+v for u,v in zip(e,f));out[g]=out.get(g,0)+x*y
  else:
   out=dict(a);sign=-1 if kind=='-' else 1
   for e,y in b.items():out[e]=out.get(e,0)+sign*y
  return {e:c for e,c in out.items() if c}
 def digest(self,p):return sha(canonical([[list(e),hex(c)] for e,c in sorted(p.items())]))
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def square(self,a):return self.mul(a,a)


def cut_proof(p,sync=None):
 r=Ring(STATE+(['Q','D']+COLS if sync is None else ['n','next_n','P']))
 v={name:r.v(name) for name in r.names};env={k:v[k] for k in STATE}
 if sync is None:
  env['C:D']=v['D'];env[p['selector_polynomial']]=v['Q'];env.update({wire:v[col] for col,wire in p['lookup_wires'].items()})
  expected=r.square(v['Q']);tail=p['instructions'][p['lookup_end']:]
  for off,kind in [(0,'K'),(2,'G')]:
   for j in [0,1]:
    pred=r.add(r.mul(v[STATE[off]],v[kind+str(j)]),r.mul(v[STATE[off+1]],v[kind+str(j+2)]))
    res=r.sub(r.mul(v['D'],v[STATE[4+off+j]]),pred);expected=r.add(expected,r.square(res))
 else:
  env.update({k:v[k] for k in ['n','next_n']});env[p['parent_tile_output']]=v['P']
  residuals=[r.sub(v['next_x0'],v['x0']),r.sub(v['next_x1'],v['x1']),
   r.sub(v['next_y0'],r.add(r.mul(52891,v['y0']),r.mul(94920,v['y1']))),
   r.sub(v['next_y1'],r.add(r.mul(-29036,v['y0']),r.mul(-52109,v['y1']))),
   r.sub(r.sub(v['n'],v['next_n']),1)]
  load=r.c(0)
  for e in residuals:load=r.add(load,r.square(e))
  tile=r.add(r.add(v['P'],r.square(v['n'])),r.square(v['next_n']))
  expected=r.mul(load,tile);tail=p['instructions'][len(sync['instructions']):]
 out=run_rows(tail,env,r.op)
 need(out[p['output']]==expected,'whole paid coefficient cut')
 if sync is not None:need(out[p['loader_factor']]==load and out[p['tile_factor']]==tile,'both wrapper factors')
 return {'independent_coefficient_terms':len(expected),'coefficient_sha256':r.digest(expected)}


def lookup_proof(p,nodes,coefs,recipe):
 # Symbolic linear combinations of the shared basis: source proof with no giant polynomial expansion.
 r=Ring(['P'+str(j) for j in range(1,96)])
 env={'selector':r.v('P1')}
 for j,wire in enumerate(p['basis_wires'][2:96],2):env[wire]=r.v('P'+str(j))
 for col in COLS:
  for j,name in enumerate(recipe['coefficient_bindings'][col]):
   if name:env[name]=r.c(coefs[col][j])
 out=run_rows(p['instructions'][190:p['lookup_end']],env,r.op)
 terms=0
 for col,wire in p['lookup_wires'].items():
  expected=r.c(coefs[col][0])
  for j in range(1,96):
   if coefs[col][j]:expected=r.add(expected,r.mul(coefs[col][j],r.v('P'+str(j))))
  need(out[wire]==expected,'complete lookup against basis coefficient table');terms+=len(expected)
 # Entire literal prefix is compared coefficientwise over an unrestricted selector.
 u=Ring(['z']);z=u.v('z');prefix_env=run_rows(p['instructions'][:190],{'selector':z},u.op)
 expected=u.c(1)
 for j,wire in enumerate(p['basis_wires']):
  actual=u.c(wire) if type(wire)is int else z if wire=='selector' else prefix_env[wire]
  need(actual==expected,'each actual falling prefix')
  if j<96:expected=u.mul(expected,u.sub(z,nodes[j]))
 Q=prefix_env[p['selector_polynomial']]
 need(max(e[0] for e in Q)==96 and Q[(96,)]==1,'monic selector polynomial')
 return {'basis_polynomials':97,'lookup_basis_coefficient_terms':terms,
  'Q_polynomial_sha256':u.digest(Q),'Q_degree':96,'Q_leading_coefficient':1}


def degree_line(p,nodes,constants):
 # Exact zero propagation in the literal DAG prunes only expressions annihilated on this line.
 # Paid source rows are not deleted: this is solely a specialization proof.
 zero={n for n in p['ports'] if n not in ['selector','n']}
 by={}
 def iszero(v):return v==0 if type(v)is int else v in zero
 for n,op,a,b in p['instructions']:
  by[n]=(op,a,b)
  if (op=='*' and (iszero(a) or iszero(b))) or (op in ['+','-'] and iszero(a) and iszero(b)):zero.add(n)
 r=Ring(['t']);env={'selector':r.v('t')}
 if 'n' in p['ports']:env['n']=r.v('t')
 evaluated=set()
 def get(v):
  if type(v)is int:return r.c(v)
  if v in zero:return r.c(0)
  if v in env:return env[v]
  if v in constants:env[v]=r.c(constants[v]);return env[v]
  op,a,b=by[v];env[v]=r.op(op,get(a),get(b));evaluated.add(v);return env[v]
 poly=get(p['output']);Q=r.c(1)
 for node in nodes:Q=r.mul(Q,r.sub(r.v('t'),node))
 expected=r.square(Q)
 if 'n' in p['ports']:expected=r.mul(r.square(r.sub(r.v('t'),1)),r.add(expected,r.square(r.v('t'))))
 need(poly==expected and max(e[0] for e in poly)==p['exact_degree'] and poly[(p['exact_degree'],)]==1,'full literal degree specialization')
 return {'substitution':'selector=t; n=t for countdown; all other supplied ports=0',
  'identity':'Q(t)^2' if 'n' not in p['ports'] else '(t-1)^2*(Q(t)^2+t^2)',
  'exact_degree':p['exact_degree'],'leading_coefficient':1,'specialized_polynomial_sha256':r.digest(poly),
  'zero_propagation_scope':'Exact specialization only; no paid source deletion.',
  'nonzero_specialization_rows_evaluated':len(evaluated)}


def numerical_checks(variants,table,nodes,constants):
 count=0;node_indexes=[0,1,2,3,17,48,95]
 for name,p in variants.items():
  for i in node_indexes:
   row=table[i];x=[2-i,3];y=[-5,1+i]
   def multiply(v,m):return [v[0]*m[0]+v[1]*m[2],v[0]*m[1]+v[1]*m[3]]
   values=dict(constants);values.update(dict(zip(STATE,x+y+multiply(x,row['K'])+multiply(y,row['G']))));values['selector']=nodes[i]
   if 'n' in p['ports']:values.update(n=0,next_n=0)
   result=run_rows(p['instructions'],values)[p['output']];need(result==0,'selected entire genuine tile source');count+=1
   values['next_x1']+=1;need(run_rows(p['instructions'],values)[p['output']]>0,'whole-source wrong row');count+=1
  for z in [Fraction(1,2),Fraction(-1,3)]:
   values=dict(constants);values.update({n:0 for n in p['ports']});values['selector']=z
   need(run_rows(p['instructions'],values)[p['output']]>0,'non-node real selector');count+=1
  if 'n' in p['ports']:
   for n in [-2,Fraction(3,2),3]:
    x=[2,-1];y=[1,2];yp=multiply(y,[52891,-29036,94920,-52109])
    values=dict(constants);values.update(dict(zip(STATE,x+y+x+yp)));values.update(selector=Fraction(1,2),n=n,next_n=n-1)
    need(run_rows(p['instructions'],values)[p['output']]==0,'loader selector unrestricted');count+=1
 ordered=sorted(nodes);negative=next(ordered[j]+1 for j in range(0,95,2) if ordered[j+1]>ordered[j]+1)
 need(math.prod(negative-z for z in nodes)<0,'integer unsquared-Q counterexample')
 return {'whole_source_checks':count,'tile_node_indexes':node_indexes,'integer_with_negative_unsquared_Q':negative,
  'scope':'All768 lookup node values are checked separately; full high-bit DAG checks are bounded to the listed nodes, wrong-row mutations, rational nonnodes and loader cases.'}


def verify(root):
 blobs={}
 for name,h in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==h,'pin '+name);blobs[name]=b
 parent=load(blobs['matrix193_newton_selector.json']);scout=load(blobs['matrix193_lookup_schedule_scout.json'])
 need(parent['source_sha256']==PINS['matrix193_newton_selector.py'],'parent self pin')
 need(scout['source_sha256']==PINS['matrix193_lookup_schedule_scout.py'],'scout self pin')
 table=parent['transition_table'];need(type(table)is list and len(table)==96,'actual96 table')
 need([r['tile_id'] for r in table]==scout['lookup_packets'][1]['selector_tile_order'],'cleanup order from scout')
 need([r['tile_id'] for r in table[:4]]==[109,110,111,112],'cleanup prefix')
 need(all(type(r['tile_id'])is int and all(type(x)is int for key in ['K','G'] for x in r[key]) for r in table),'table integer types')
 need(all(len(r[key])==4 and r[key][0]*r[key][3]-r[key][1]*r[key][2]==1 for r in table for key in ['K','G']),'integral determinant-one actions')
 nodes,constants,coefs,recipe=compile_numerals(table)
 sync=build(nodes,constants,coefs,recipe);down=append_countdown(sync,parent)
 sync['lookup_proof']=lookup_proof(sync,nodes,coefs,recipe)
 for p in [sync,down]:p['ledger']=ledger(p,constants);p['degree_certificate']=degree_line(p,nodes,constants)
 sync['formal_tail']=cut_proof(sync);down['formal_tail']=cut_proof(down,sync)
 need(sync['ledger']['total']==1527 and down['ledger']['total']==1553,'emitted full totals')
 variants={'real_synchronized':sync,'real_countdown':down}
 return {'status':'PASS_COMPLETE_REAL_SAFE_LOCAL_RELATIONS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,
  'predecessor_code_executed':False,'transition_table':table,'selector_to_tile_id':[r['tile_id'] for r in table],
  'fixed_numeral_recipe':recipe,'variants':variants,'finite_checks':numerical_checks(variants,table,nodes,constants),
  'initial_state':parent['initial_state'],'endpoint':parent['endpoint'],
  'comparison':{'parent_real_synchronized':parent['variants']['real_synchronized']['ledger'],
   'parent_real_countdown':parent['variants']['real_countdown']['ledger'],
   'saving_per_full_predicate':{'M':94,'A':94,'total':188}},
  'fixed_duration_bounds':{'synchronized':{'operations_per_step_plus_join':1528,'endpoint':5,'signed_witnesses_per_step':5,'degree_upper':192},
   'countdown':{'operations_per_step_plus_join':1554,'endpoint':7,'signed_witnesses_per_step':6,'degree_upper':194}},
  'scope':'Fixed saved matrix context and fixed arbitrary signed-integer numeral model. Complete local and fixed-duration predicates only. No unbounded fixed-arity packing, positive-coordinate conversion or universal operation bound.'}


def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path)
 mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument('--expect',type=Path);mode.add_argument('--output',type=Path)
 a=ap.parse_args();receipt=verify(a.root)
 if a.expect:need(exact(receipt,load(a.expect.read_bytes())),'type-exact receipt mismatch')
 else:
  with a.output.open('x') as f:f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':receipt['status'],'ledgers':{k:v['ledger'] for k,v in receipt['variants'].items()},'numeral_bits':receipt['fixed_numeral_recipe']['common_scale_bits'],'checks':receipt['finite_checks']['whole_source_checks']}))
if __name__=='__main__':main()
