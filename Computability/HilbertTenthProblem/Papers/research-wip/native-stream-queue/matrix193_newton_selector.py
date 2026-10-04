#!/usr/bin/env python3
"""Fresh fully paid matrix-selector compiler. Predecessors are inert data."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

PINS={
 'matrix193_grouped_row_choices.py':'b2d850448f71ea8af8fc3bee3f3a95cb073f14ea1e65c8403618ebbf1bce3da6',
 'matrix193_grouped_row_choices.json':'d70f8038b4110c3a8ce7579071dc779782958e69347bba7f628026b16521d260',
 'matrix193_grouped_row_choices.md':'aa84987b2d28ed4b7c28ef0b8af6ce3c9f0de288415081834a37a169f8afc0f8',
 'matrix193_countdown_rows.py':'5a1d373933f43b9f94dc54cf276aaa865fc6c82a1a25082842d8d4690e668577',
 'matrix193_countdown_rows.json':'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0',
 'matrix193_countdown_rows.md':'93363ca2f21949e2c7fa6d2bd4052b2219ec06fe4c2d52ba317fc19a229c5361',
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
class Source:
 def __init__(self):self.rows=[];self.memo={}
 def op(self,o,a,b):
  if type(a)is int and type(b)is int:return a*b if o=='*' else a+b if o=='+' else a-b
  if o=='*' and (a==0 or b==0):return 0
  if o=='*' and a==1:return b
  if o=='*' and b==1:return a
  if o=='+' and a==0:return b
  if o in ['+','-'] and b==0:return a
  if o in ['+','*'] and repr(a)>repr(b):a,b=b,a
  key=(o,a,b)
  if key not in self.memo:
   n='r'+str(len(self.rows));self.rows.append([n,o,a,b]);self.memo[key]=n
  return self.memo[key]
 def sum(self,xs):
  s=xs[0]
  for x in xs[1:]:s=self.op('+',s,x)
  return s
def coefficients(values,D):
 row=list(values);out=[]
 for j in range(len(values)):
  need(D%math.factorial(j)==0,'integral common denominator')
  out.append(D//math.factorial(j)*row[0]);row=[b-a for a,b in zip(row,row[1:])]
 return out
def build(table,square_selector):
 D=math.factorial(95);e=Source();basis=[1,'selector'];shifts={}
 for j in range(1,96):
  shifts[j]=e.op('-','selector',j);basis.append(e.op('*',basis[-1],shifts[j]))
 wires={};cs={}
 for col in COLS:
  values=[r[col[0]][int(col[1])] for r in table];cs[col]=coefficients(values,D)
  terms=[e.op('*',c,basis[j]) for j,c in enumerate(cs[col]) if c]
  wires[col]=e.sum(terms)
 split=len(e.rows);res=[]
 for offset,kind in [(0,'K'),(2,'G')]:
  for j in [0,1]:
   prediction=e.op('+',e.op('*',STATE[offset],wires[kind+str(j)]),e.op('*',STATE[offset+1],wires[kind+str(j+2)]))
   res.append(e.op('-',e.op('*',D,STATE[4+offset+j]),prediction))
 Q=basis[96];qterm=e.op('*',Q,Q) if square_selector else Q
 output=e.sum([qterm]+[e.op('*',r,r) for r in res])
 return {'ports':STATE+['selector'],'instructions':e.rows,'output':output,'lookup_end':split,'lookup_wires':wires,'scaled_newton_coefficients':cs,'common_scale':D,'basis_wires':basis,'residuals':res,'selector_root_polynomial':Q,'square_selector':square_selector,'extra_selector_witnesses':1,'exact_degree':192,'domain':'signed reals or integers' if square_selector else 'signed integers only','fixed_numeral_convention':'Arbitrary fixed signed integer literals are free leaves; every nonconstant multiplication, addition and subtraction is charged. Coefficient bit cost is separately recorded.'}
def ledger(p):
 known=set(p['ports']);producers={};degrees={n:1 for n in known}
 for n,o,a,b in p['instructions']:
  need(n not in known and o in ['+','-','*'],'producer')
  need(all(type(t)is int or t in known for t in [a,b]),'closure')
  da=0 if type(a)is int else degrees[a];db=0 if type(b)is int else degrees[b]
  degrees[n]=da+db if o=='*' else max(da,db);known.add(n);producers[n]=[a,b]
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo+=producers.get(n,[])
 need(live==set(producers)|set(p['ports']),'all rows and ports live')
 m=sum(r[1]=='*' for r in p['instructions']);a=len(p['instructions'])-m
 need(degrees[p['output']]==p['exact_degree'],'upper degree')
 return {'M':m,'A':a,'total':m+a,'all_rows_and_ports_live':True}
def add(a,b,sign=1):
 r=[0]*max(len(a),len(b))
 for j,v in enumerate(a):r[j]+=v
 for j,v in enumerate(b):r[j]+=sign*v
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def polyop(o,a,b):
 a=[a] if type(a)is int else a;b=[b] if type(b)is int else b
 return mul(a,b) if o=='*' else add(a,b,-1 if o=='-' else 1)
def evaluate(rows,values,op=None):
 e=dict(values)
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=op(o,a,b) if op else a*b if o=='*' else a+b if o=='+' else a-b
 return e
def at(poly,x):
 v=0
 for c in reversed(poly):v=v*x+c
 return v
def audit_lookup(p,table):
 e=evaluate(p['instructions'][:p['lookup_end']],{'selector':[0,1]},polyop);D=p['common_scale'];checks=0
 for j,b in enumerate(p['basis_wires']):
  poly=[b] if type(b)is int else e[b] if b!='selector' else [0,1]
  expected=[1]
  for k in range(j):expected=mul(expected,[-k,1])
  need(poly==expected,'exact falling basis')
 for col,wire in p['lookup_wires'].items():
  poly=[wire] if type(wire)is int else e[wire]
  need(len(poly)<=96,'lookup degree')
  for j,row in enumerate(table):need(at(poly,j)==D*row[col[0]][int(col[1])],'exact96-node lookup');checks+=1
 return {'all_basis_coefficients_checked':97,'node_value_equalities':checks,'lookup_degrees':{c:len(e[w])-1 for c,w in p['lookup_wires'].items()},'lookup_polynomial_sha256':{c:sha(canonical(e[w])) for c,w in p['lookup_wires'].items()},'maximum_scaled_newton_coefficient_bits':max(abs(x).bit_length() for cs in p['scaled_newton_coefficients'].values() for x in cs),'common_scale_bits':D.bit_length(),'zero_nonconstant_coefficients':{c:[j for j,x in enumerate(cs) if j and not x] for c,cs in p['scaled_newton_coefficients'].items()}}
def countdown(p,parent):
 old=parent['variants']['countdown'];oldsync=parent['variants']['synchronized'];rows=copy.deepcopy(p['instructions']);rename={oldsync['output']:p['output']}
 for n,o,a,b in old['instructions'][len(oldsync['instructions']):]:
  out='r'+str(len(rows));rows.append([out,o,rename.get(a,a),rename.get(b,b)]);rename[n]=out
 need(len(rows)-len(p['instructions'])==26,'entire paid loader suffix')
 return {'ports':STATE+['selector','n','next_n'],'instructions':rows,'output':rename[old['output']],'parent_tile_output':p['output'],'loader_factor':rename[old['loader_factor']],'tile_factor':rename[old['tile_factor']],'extra_selector_witnesses':1,'exact_degree':194,'domain':p['domain'],'square_selector':p['square_selector']}
def degrees(p):
 v={n:[0] for n in p['ports']};v['selector']=[0,1];v['x0']=[0,1]
 if 'n' in v:v['n']=[0,1]
 e=evaluate(p['instructions'],v,polyop);poly=e[p['output']]
 need(len(poly)-1==p['exact_degree'] and poly[-1]>0,'full degree line')
 return {'substitution':'selector=x0=t; n=t for countdown; every other supplied port=0','exact_degree':len(poly)-1,'leading_coefficient':poly[-1],'whole_univariate_polynomial_sha256':sha(canonical(poly))}
def row(v,m):return [v[0]*m[0]+v[1]*m[2],v[0]*m[1]+v[1]*m[3]]
def value(p,assignment):return evaluate(p['instructions'],assignment)[p['output']]
def formal_tail(p,sync=None):
 # Independent sparse coefficient calculation at the entire paid residual/wrapper cut.
 def c(x):return {():x} if x else {}
 def var(x):return {(x,):1}
 def plus(a,b,sign=1):
  out=dict(a)
  for m,v in b.items():out[m]=out.get(m,0)+sign*v
  return {m:v for m,v in out.items() if v}
 def times(a,b):
  out={}
  for m,u in a.items():
   for n,v in b.items():
    k=tuple(sorted(m+n));out[k]=out.get(k,0)+u*v
  return {m:v for m,v in out.items() if v}
 def operate(o,a,b):
  a=c(a) if type(a)is int else a;b=c(b) if type(b)is int else b
  return times(a,b) if o=='*' else plus(a,b,-1 if o=='-' else 1)
 env={n:var(n) for n in p['ports']};expected={}
 if sync is None:
  for col,wire in p['lookup_wires'].items():env[wire]=var(col)
  env[p['selector_root_polynomial']]=var('Q')
  expected=times(var('Q'),var('Q')) if p['square_selector'] else var('Q')
  for off,kind in [(0,'K'),(2,'G')]:
   for j in [0,1]:
    pred=plus(times(var(STATE[off]),var(kind+str(j))),times(var(STATE[off+1]),var(kind+str(j+2))))
    residual=plus(times(c(p['common_scale']),var(STATE[4+off+j])),pred,-1)
    expected=plus(expected,times(residual,residual))
  tail=p['instructions'][p['lookup_end']:]
 else:
  env[p['parent_tile_output']]=var('P');tail=p['instructions'][len(sync['instructions']):]
  load={};B=[52891,-29036,94920,-52109]
  residuals=[plus(var('next_x0'),var('x0'),-1),plus(var('next_x1'),var('x1'),-1)]
  for j in [0,1]:residuals.append(plus(var(STATE[6+j]),plus(times(c(B[j]),var('y0')),times(c(B[j+2]),var('y1'))),-1))
  residuals.append(plus(plus(var('n'),var('next_n'),-1),c(1),-1))
  for r in residuals:load=plus(load,times(r,r))
  tile=plus(plus(var('P'),times(var('n'),var('n'))),times(var('next_n'),var('next_n')))
  expected=times(load,tile)
 out=evaluate(tail,env,operate)
 need(out[p['output']]==expected,'complete formal paid tail')
 if sync is not None:need(out[p['loader_factor']]==load and out[p['tile_factor']]==tile,'both exact loader/tile factors')
 return {'independent_coefficient_terms':len(expected),'coefficient_sha256':sha(canonical(sorted(expected.items())))}
def checks(variants,table):
 count=0
 for name,p in variants.items():
  for j,tile in enumerate(table):
   x=[-2,3];y=[5,-7];v=dict(zip(STATE,x+y+row(x,tile['K'])+row(y,tile['G'])));v['selector']=j
   if 'n' in p['ports']:v.update(n=0,next_n=0)
   need(value(p,v)==0,'every actual tile');count+=1
   v['next_x0']+=1
   need(value(p,v)>0,'single erroneous scaled row');count+=1
  for z in [-2,-1,96,97]:
   v={n:0 for n in p['ports']};v['selector']=z
   # For countdown at n=n'=0 the loader has its nonzero counter residual.
   need(value(p,v)>0,'selector outside range');count+=1
  if 'n'in p['ports']:
   for n in [-2,0,1,3]:
    x=[-2,3];y=[5,-7];v=dict(zip(STATE,x+y+x+row(y,[52891,-29036,94920,-52109])));v.update(selector=-3,n=n,next_n=n-1)
    need(value(p,v)==0,'LOAD needs no selector restriction');count+=1
  if p['square_selector']:
   v={n:Fraction(0) for n in p['ports']};v['selector']=Fraction(1,2)
   need(value(p,v)>0,'noninteger real selector excluded on tile');count+=1
 Qhalf=math.prod(Fraction(1,2)-j for j in range(96));need(Qhalf<0,'integer-only real-domain counterexample')
 return {'whole_source_zero_or_strict_nonzero_checks':count,'integer_variant_real_counterexample':{'selector':'1/2','Q_sign':'negative','state':'all state coordinates zero except next_x0=sqrt(-Q(1/2))/95!; n=next_n=0 in countdown','conclusion':'integer-only source vanishes over reals although X=0 cannot transition to nonzero X; not claimed real sound'}}
def run(root):
 data={}
 for n,h in PINS.items():
  b=(root/n).read_bytes();need(sha(b)==h,'pin '+n);data[n]=b
 parent=load(data['matrix193_grouped_row_choices.json']);down=load(data['matrix193_countdown_rows.json']);table=parent['transition_table']
 need(len(table)==96 and down['transitions']['tiles']==table,'actual96 table')
 by={r['tile_id']:r for r in table};first=[109,110,111,112];ordered=[by[i] for i in first]+[r for r in table if r['tile_id'] not in first]
 need(len(by)==96 and sorted(r['tile_id'] for r in ordered)==sorted(by),'exact96-tile partition')
 need(all(by[i]['K']==by[first[0]]['K'] for i in first),'identical cleanup upper actions')
 variants={};audits={};baseline={}
 for name,square in [('real',True),('integer',False)]:
  old=build(table,square);old['ledger']=ledger(old);baseline[name]={'ledger':old['ledger'],'full_source_sha256':sha(canonical(old['instructions'])),'scope':'Generated and liveness-audited comparison schedule; full rows saved only for optimized variants.'}
  p=build(ordered,square);p['ledger']=ledger(p);audits[name]=audit_lookup(p,ordered)
  need(old['ledger']['total']-p['ledger']['total']==24,'cleanup-prefix24-gate saving')
  p['formal_tail']=formal_tail(p)
  variants[name+'_synchronized']=p;cp=countdown(p,parent);cp['ledger']=ledger(cp);cp['formal_tail']=formal_tail(cp,p);variants[name+'_countdown']=cp
 for p in variants.values():p['degree_certificate']=degrees(p)
 return {'status':'PASS_EXACT_EXISTENTIAL_LOCAL_RELATIONS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'predecessor_code_executed':False,'transition_table':ordered,'selector_to_tile_id':[r['tile_id'] for r in ordered],'baseline_original_order':baseline,'variants':variants,'lookup_audits':audits,'finite_checks':checks(variants,ordered),'initial_state':parent['initial_state'],'endpoint':parent['endpoint'],'fixed_duration_bounds':{k:{'steps_coefficient':p['ledger']['total']+1,'constant':7 if 'countdown'in k else 5,'signed_witnesses_per_step':6 if 'countdown'in k else 5,'degree_upper':p['exact_degree']} for k,p in variants.items()},'scope':'Fixed saved matrix context, one additional existential signed selector per step, fixed-numeral cost model. Local or fixed-duration only; no unbounded fixed-arity history packing or positive-witness conversion paid. No new complete universal polynomial bound.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.root.resolve());s=json.dumps(r,sort_keys=True,indent=2)+'\n'
 if a.expect:need(a.expect.read_text()==s,'exact receipt replay')
 else:
  with a.output.open('x') as f:f.write(s)
 print(json.dumps({'status':r['status'],'ledgers':{k:v['ledger'] for k,v in r['variants'].items()},'checks':r['finite_checks']['whole_source_zero_or_strict_nonzero_checks']}))
if __name__=='__main__':main()
