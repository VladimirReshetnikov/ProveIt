#!/usr/bin/env python3
"""Independent bounded source/cut review; all author and predecessor files are inert."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

AUTHOR = {
 'matrix193_newton_selector.py':'a8437280c24b844f7cd0c5193ba9421a5be6e93901027023440709d7c74c3eb0',
 'matrix193_newton_selector.json':'21c47a877d2b36a435c3ffd7dbdb46a21a6c96f11c91d60637743ef20f3fbeff',
 'matrix193_newton_selector.md':'b5cd29a950c1e380969bb3a7cfe924b78a360e7ab2f61fff82151dc627de581e'}
PARENTS = {
 'matrix193_grouped_row_choices.py':'b2d850448f71ea8af8fc3bee3f3a95cb073f14ea1e65c8403618ebbf1bce3da6',
 'matrix193_grouped_row_choices.json':'d70f8038b4110c3a8ce7579071dc779782958e69347bba7f628026b16521d260',
 'matrix193_grouped_row_choices.md':'aa84987b2d28ed4b7c28ef0b8af6ce3c9f0de288415081834a37a169f8afc0f8',
 'matrix193_countdown_rows.py':'5a1d373933f43b9f94dc54cf276aaa865fc6c82a1a25082842d8d4690e668577',
 'matrix193_countdown_rows.json':'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0',
 'matrix193_countdown_rows.md':'93363ca2f21949e2c7fa6d2bd4052b2219ec06fe4c2d52ba317fc19a229c5361'}
STATES=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
COLUMNS=['K0','K1','K2','K3','G0','G1','G2','G3']


def check(b, message):
 if not b: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def load(b):
 def object_pairs(items):
  out={}
  for k,v in items:
   check(k not in out,'duplicate key');out[k]=v
  return out
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(b,object_pairs_hook=object_pairs,parse_float=bad,parse_constant=bad)
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b


class Ring:
 def __init__(self,names):self.names=names;self.zero=(0,)*len(names)
 def const(self,c):return {self.zero:c} if c else {}
 def var(self,name):
  e=list(self.zero);e[self.names.index(name)]=1;return {tuple(e):1}
 def op(self,op,a,b):
  if type(a)is int:a=self.const(a)
  if type(b)is int:b=self.const(b)
  out={}
  if op=='*':
   for e,x in a.items():
    for f,y in b.items():
     g=tuple(u+v for u,v in zip(e,f));out[g]=out.get(g,0)+x*y
  else:
   out=dict(a);sign=-1 if op=='-' else 1
   for e,y in b.items():out[e]=out.get(e,0)+sign*y
  return {e:c for e,c in out.items() if c}
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def square(self,a):return self.mul(a,a)
 def digest(self,p):return sha(json.dumps(sorted(p.items()),separators=(',',':')).encode())


def execute(rows,values,ring=None):
 values=dict(values)
 for name,op,a,b in rows:
  a=a if type(a)is int else values[a];b=b if type(b)is int else values[b]
  values[name]=ring.op(op,a,b) if ring else a*b if op=='*' else a+b if op=='+' else a-b
 return values


def live_ledger(p):
 known=set(p['ports']);used=set();by={};degree={k:1 for k in known}
 for name,op,a,b in p['instructions']:
  check(type(name)is str and name not in known and op in ['+','-','*'],'producer')
  check(all(type(v)is int or type(v)is str and v in known for v in [a,b]),'source closure')
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b]
  degree[name]=da+db if op=='*' else max(da,db);by[name]=(a,b);known.add(name)
 pending=[p['output']]
 while pending:
  v=pending.pop()
  if type(v)is int or v in used:continue
  used.add(v);pending.extend(by.get(v,()))
 check(used==set(by)|set(p['ports']),'liveness')
 m=sum(r[1]=='*' for r in p['instructions']);a=len(p['instructions'])-m
 check(p['ledger']=={'M':m,'A':a,'total':m+a,'all_rows_and_ports_live':True},'ledger')
 check(degree[p['output']]==p['exact_degree'],'upper degree')
 return {'M':m,'A':a,'total':m+a}


def inspect_lookup(p,table):
 ring=Ring(['z']);z=ring.var('z')
 env=execute(p['instructions'][:p['lookup_end']],{'selector':z},ring)
 check(p['common_scale']==math.factorial(95),'common scale');D=p['common_scale']
 expected=ring.const(1)
 for j,wire in enumerate(p['basis_wires']):
  actual=ring.const(wire) if type(wire)is int else z if wire=='selector' else env[wire]
  check(actual==expected,'prefix exact polynomial')
  expected=ring.mul(expected,ring.sub(z,j))
 checks=0;degrees={}
 for column,wire in p['lookup_wires'].items():
  poly=env[wire];degrees[column]=max(e[0] for e in poly)
  check(degrees[column]==95,'lookup degree95')
  for node,row in enumerate(table):
   actual=sum(c*node**e[0] for e,c in poly.items())
   check(actual==D*row[column[0]][int(column[1])],'independent lookup polynomial/node value');checks+=1
 return {'node_column_values':checks,'degrees':degrees,'whole_column_digests':{c:ring.digest(env[w]) for c,w in p['lookup_wires'].items()}}


def inspect_cut(p,sync=None):
 names=STATES+(['Q']+COLUMNS if sync is None else ['n','next_n','P'])
 r=Ring(names);v={n:r.var(n) for n in names}
 if sync is None:
  env={k:v[k] for k in STATES}
  env.update({wire:v[col] for col,wire in p['lookup_wires'].items()});env[p['selector_root_polynomial']]=v['Q']
  expected=r.square(v['Q']) if p['square_selector'] else v['Q'];tail=p['instructions'][p['lookup_end']:]
  for a,b,n0,n1,kind in [('x0','x1','next_x0','next_x1','K'),('y0','y1','next_y0','next_y1','G')]:
   for j,n in enumerate([n0,n1]):
    error=r.sub(r.mul(p['common_scale'],v[n]),r.add(r.mul(v[a],v[kind+str(j)]),r.mul(v[b],v[kind+str(j+2)])))
    expected=r.add(expected,r.square(error))
 else:
  env={k:v[k] for k in STATES+['n','next_n']};env[p['parent_tile_output']]=v['P']
  residuals=[r.sub(v['next_x0'],v['x0']),r.sub(v['next_x1'],v['x1']),
   r.sub(v['next_y0'],r.add(r.mul(52891,v['y0']),r.mul(94920,v['y1']))),
   r.sub(v['next_y1'],r.add(r.mul(-29036,v['y0']),r.mul(-52109,v['y1']))),
   r.sub(r.sub(v['n'],v['next_n']),1)]
  load=r.const(0)
  for a in residuals:load=r.add(load,r.square(a))
  tile=r.add(r.add(v['P'],r.square(v['n'])),r.square(v['next_n']))
  expected=r.mul(load,tile);tail=p['instructions'][len(sync['instructions']):]
 out=execute(tail,env,r)
 check(out[p['output']]==expected,'complete residual/finalizer cut')
 if sync is not None:check(out[p['loader_factor']]==load and out[p['tile_factor']]==tile,'wrapper factors')
 return {'coefficient_entries':len(expected),'polynomial_sha256':r.digest(expected)}


def inspect_degree(p):
 ring=Ring(['t']);values={name:ring.const(0) for name in p['ports']}
 values['selector']=values['x0']=ring.var('t')
 if 'n' in values:values['n']=ring.var('t')
 poly=execute(p['instructions'],values,ring)[p['output']];d=max(e[0] for e in poly)
 check(d==p['exact_degree'] and poly[(d,)]>0,'whole source exact degree')
 check(poly[(d,)]==p['degree_certificate']['leading_coefficient'],'author degree leader')
 return {'degree':d,'leading_coefficient':poly[(d,)],'polynomial_sha256':ring.digest(poly)}


def verify(root,author_root):
 raw={}
 for directory,pins in [(root,PARENTS),(author_root,AUTHOR)]:
  for name,h in pins.items():
   b=(directory/name).read_bytes();check(sha(b)==h,'pin '+name);raw[name]=b
 author=load(raw['matrix193_newton_selector.json']);parent=load(raw['matrix193_grouped_row_choices.json']);down=load(raw['matrix193_countdown_rows.json'])
 check(author['source_sha256']==AUTHOR['matrix193_newton_selector.py'] and author['pins']==PARENTS,'author self/dependency pins')
 table=parent['transition_table'];check(table==down['transitions']['tiles'],'parent table identity')
 by={r['tile_id']:r for r in table};first=[109,110,111,112]
 ordered=[by[i] for i in first]+[r for r in table if r['tile_id'] not in first]
 check(author['transition_table']==ordered and author['selector_to_tile_id']==[r['tile_id'] for r in ordered],'full paired table permutation')
 check(author['initial_state']==parent['initial_state'] and author['endpoint']==parent['endpoint'],'initializer and endpoint unchanged')
 variants=author['variants'];results={}
 for name,p in variants.items():
  results[name]={'ledger':live_ledger(p),'degree':inspect_degree(p)}
  if name.endswith('synchronized'):
   results[name]['lookup']=inspect_lookup(p,ordered);results[name]['cut']=inspect_cut(p)
  else:
   sync=variants[name.replace('countdown','synchronized')]
   check(p['instructions'][:len(sync['instructions'])]==sync['instructions'],'literal complete synchronized prefix')
   oldsync=parent['variants']['synchronized'];oldcount=parent['variants']['countdown']
   rename={oldsync['output']:sync['output']};actual=p['instructions'][len(sync['instructions']):]
   expected=[]
   for name0,op,a,b in oldcount['instructions'][len(oldsync['instructions']):]:
    name1='r'+str(len(sync['instructions'])+len(expected));expected.append([name1,op,rename.get(a,a),rename.get(b,b)]);rename[name0]=name1
   check(actual==expected and len(actual)==26,'every inherited loader row')
   results[name]['cut']=inspect_cut(p,sync)
 real=variants['real_synchronized'];integer=variants['integer_synchronized']
 check(real['instructions'][:real['lookup_end']]==integer['instructions'][:integer['lookup_end']],'same full lookup cone')
 checks=0
 for mode,p in variants.items():
  for j,tile in enumerate(ordered):
   x=[j-47,2-j];y=[3*j-7,11-j]
   def row(v,m):return [v[0]*m[0]+v[1]*m[2],v[0]*m[1]+v[1]*m[3]]
   values=dict(zip(STATES,x+y+row(x,tile['K'])+row(y,tile['G'])));values['selector']=j
   if 'n' in p['ports']:values.update(n=0,next_n=0)
   check(execute(p['instructions'],values)[p['output']]==0,'all matched tiles');checks+=1
   values['next_y1']+=2
   check(execute(p['instructions'],values)[p['output']]>0,'wrong next coordinate');checks+=1
  for z in [-10,-1,96,98,100]:
   values={v:0 for v in p['ports']};values['selector']=z
   check(execute(p['instructions'],values)[p['output']]>0,'outside selector');checks+=1
 Qhalf=math.prod(Fraction(1,2)-j for j in range(96));check(Qhalf<0,'real counterexample sign')
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR,'parent_pins':PARENTS,
  'predecessor_or_author_code_executed_by_this_helper':False,'variants':results,
  'total_paid_rows':sum(x['ledger']['total'] for x in results.values()),
  'complete_node_column_values':1536,'whole_source_zero_or_nonzero_checks':checks,
  'formal_cut_coefficient_entries':sum(x['cut']['coefficient_entries'] for x in results.values()),
  'scope':'Independent full four-array, coefficient-cut and degree review; unrestricted proofs are in the companion note. No unbounded product packing or universal bound.'}


def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',required=True,type=Path);p.add_argument('--author-root',type=Path)
 m=p.add_mutually_exclusive_group(required=True);m.add_argument('--output',type=Path);m.add_argument('--expect',type=Path);a=p.parse_args()
 receipt=verify(a.root,a.author_root or a.root)
 if a.expect:check(same(receipt,load(a.expect.read_bytes())),'review receipt mismatch')
 else:
  with a.output.open('x') as f:f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 print('PASS:',receipt['total_paid_rows'],'rows;',receipt['formal_cut_coefficient_entries'],'cut coefficients;',receipt['whole_source_zero_or_nonzero_checks'],'whole-source checks')
if __name__=='__main__':main()
