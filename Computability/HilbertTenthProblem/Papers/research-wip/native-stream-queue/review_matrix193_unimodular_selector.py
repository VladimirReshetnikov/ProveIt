#!/usr/bin/env python3
"""Independent fixed-numeral, full-array and unimodular residual audit."""
import argparse,hashlib,json,math
from pathlib import Path
PINS={'matrix193_unimodular_selector.py':'34c98040cf2d20d88fbfdfe7e71ae88d6904547a5ab8102c0805c71d6bccc456','matrix193_unimodular_selector.json':'c03bc63e10398bb53e19fd1ad6f755fa132164379dce10c523de3ea0dd598e1c','matrix193_unimodular_selector.md':'87ee28420daa8d722b495137a9e76b316a74e95c64c94f656f592849f06640b2'}
STATE=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
COLS=['K0','K1','K2','G0','G1','G2']
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(b):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(s):raise ValueError('noninteger JSON '+s)
 return json.loads(b,object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def meta(v):return {'sign':(v>0)-(v<0),'magnitude_bits':abs(v).bit_length(),'signed_magnitude_sha256':sha((b'-' if v<0 else b'+')+abs(v).to_bytes((abs(v).bit_length()+7)//8,'big'))}
def rows_eval(rows,env,op):
 e=dict(env)
 for name,kind,a,b in rows:
  av=a if type(a)is int else e[a];bv=b if type(b)is int else e[b]
  e[name]=op(kind,av,bv)
 return e
class Poly:
 def __init__(self,names):self.names=names;self.zero=(0,)*len(names)
 def c(self,x):return {self.zero:x} if x else {}
 def v(self,x):
  e=list(self.zero);e[self.names.index(x)]=1;return {tuple(e):1}
 def op(self,kind,a,b):
  if type(a)is int:a=self.c(a)
  if type(b)is int:b=self.c(b)
  out=dict(a) if kind!='*' else {}
  if kind=='*':
   for ea,ca in a.items():
    for eb,cb in b.items():
     e=tuple(x+y for x,y in zip(ea,eb));out[e]=out.get(e,0)+ca*cb
  else:
   need(kind in ['+','-'],'polynomial operation')
   for e,c in b.items():out[e]=out.get(e,0)+(c if kind=='+' else -c)
  return {e:c for e,c in out.items() if c}
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sq(self,a):return self.mul(a,a)
def verify(root,author):
 need(len(PINS)==3,'three frozen author pins')
 raw={}
 for n,h in PINS.items():
  b=(author/n).read_bytes();need(sha(b)==h,'author pin '+n);raw[n]=b
 a=load(raw['matrix193_unimodular_selector.json'])
 need(a['source_sha256']==PINS['matrix193_unimodular_selector.py'],'self source pin')
 for n,h in a['pins'].items():need(sha((root/n).read_bytes())==h,'dependency '+n)
 parent=load((root/'matrix193_irregular_selector.json').read_bytes())
 table=a['transition_table'];recipe=a['fixed_numeral_recipe'];nodes=recipe['nodes']
 need(table==parent['transition_table'],'literal finite table')
 need(nodes==parent['fixed_numeral_recipe']['nodes'],'literal selector nodes')
 need(a['initial_state']==parent['initial_state'] and a['endpoint']==parent['endpoint'],'literal endpoints')
 pivots=[]
 for row in table:
  for key in ['K','G']:
   aa,bb,cc,dd=row[key];need(aa*dd-bb*cc==1 and aa!=0,'determinant and nonzero pivot');pivots.append(aa)
 # Reconstruct every coefficient by the closed formula, not divided differences.
 D=math.lcm(*(abs(math.prod(nodes[i]-nodes[k] for k in range(96) if k!=i)) for i in range(96)))
 constants={'C:D':D};coefficients={c:[] for c in COLS};den=[];divisions=0
 for j in range(96):
  den=[v*(nodes[i]-nodes[j]) for i,v in enumerate(den)]
  den.append(math.prod(nodes[j]-nodes[k] for k in range(j)))
  weights=[]
  for d in den:
   q,r=divmod(D,d);need(r==0,'exact fixed-data quotient');weights.append(q);divisions+=1
  for c in COLS:
   value=sum(table[i][c[0]][int(c[1])]*weights[i] for i in range(j+1));coefficients[c].append(value)
   binding=recipe['coefficient_bindings'][c][j]
   need((binding is None)==(value==0),'zero binding')
   if binding:need(binding=='C:'+c+':'+str(j),'binding name');constants[binding]=value
 need({k:meta(v) for k,v in constants.items()}==recipe['fixed_numeral_metadata'],'all exact numerals')
 sync=a['variants']['real_synchronized'];down=a['variants']['real_countdown']
 need(sync['instructions'][:190]==parent['variants']['real_synchronized']['instructions'][:190],'literal complete basis')
 # All lookup instructions as unrestricted linear combinations of basis symbols.
 lin=Poly(['P'+str(j) for j in range(1,96)])
 env={k:lin.c(v) for k,v in constants.items()}
 for j,wire in enumerate(sync['basis_wires'][1:96],1):env[wire]=lin.v('P'+str(j))
 e=rows_eval(sync['instructions'][190:sync['lookup_end']],env,lin.op)
 for c,wire in sync['lookup_wires'].items():
  need(c in COLS,'only six retained columns');expected=lin.c(coefficients[c][0])
  for j in range(1,96):expected=lin.add(expected,lin.mul(coefficients[c][j],lin.v('P'+str(j))))
  need(e[wire]==expected,'complete lookup polynomial')
 need(set(sync['lookup_wires'])==set(COLS),'six live lookups')
 # Independently expand all actual residuals and final SOS at free cut ports.
 p=Poly(STATE+COLS+['D','Q']);v={x:p.v(x) for x in p.names}
 env={x:v[x] for x in STATE};env['C:D']=v['D'];env[sync['selector_polynomial']]=v['Q']
 for col,wire in sync['lookup_wires'].items():env[wire]=v[col]
 e=rows_eval(sync['instructions'][sync['lookup_end']:],env,p.op);expected=p.sq(v['Q']);res=[]
 for key,off in [('K',0),('G',2)]:
  u,w,nu,nw=[v[STATE[j]] for j in [off,off+1,off+4,off+5]]
  A,B,C=[v[key+str(j)] for j in range(3)]
  r0=p.sub(p.mul(v['D'],nu),p.add(p.mul(A,u),p.mul(C,w)))
  r1=p.sub(p.sub(p.mul(A,nw),p.mul(B,nu)),p.mul(v['D'],w))
  res.extend([r0,r1]);expected=p.add(expected,p.add(p.sq(r0),p.sq(r1)))
 need(e[sync['output']]==expected,'whole unrestricted synchronized SOS')
 for wire,r in zip(sync['residual_wires'],res):need(e[wire]==r,'literal residual output')
 # Formal residual change-of-basis identity with determinant defect explicit.
 f=Poly(['a','b','c','d','u','w','nu','nw','D']);t={x:f.v(x) for x in f.names}
 e0=f.sub(t['nu'],f.add(f.mul(t['a'],t['u']),f.mul(t['c'],t['w'])))
 e1=f.sub(t['nw'],f.add(f.mul(t['b'],t['u']),f.mul(t['d'],t['w'])))
 r1=f.mul(t['D'],f.sub(f.sub(f.mul(t['a'],t['nw']),f.mul(t['b'],t['nu'])),t['w']))
 transformed=f.mul(t['D'],f.sub(f.mul(t['a'],e1),f.mul(t['b'],e0)))
 defect=f.mul(f.mul(t['D'],t['w']),f.sub(f.sub(f.mul(t['a'],t['d']),f.mul(t['b'],t['c'])),1))
 need(f.sub(r1,transformed)==defect,'unrestricted determinant-defect identity')
 # Full inherited 26-row loader wrapper.
 oldsync=parent['variants']['real_synchronized'];olddown=parent['variants']['real_countdown']
 rename={oldsync['output']:sync['output']};suffix=[]
 for n,op,l,r in olddown['instructions'][len(oldsync['instructions']):]:
  new='g'+str(len(sync['instructions'])+len(suffix));suffix.append([new,op,rename.get(l,l),rename.get(r,r)]);rename[n]=new
 need(len(suffix)==26 and down['instructions']==sync['instructions']+suffix,'whole countdown suffix')
 ledgers={};modchecks=0
 for name,vv in a['variants'].items():
  known=set(vv['ports'])|set(constants);producers={};M=0;degree={x:1 for x in vv['ports']};degree.update({x:0 for x in constants})
  for n,op,l,r in vv['instructions']:
   need(n not in known and op in ['+','-','*'],'row')
   need(all(type(x)is int or type(x)is str and x in known for x in [l,r]),'closure')
   dl=0 if type(l)is int else degree[l];dr=0 if type(r)is int else degree[r]
   degree[n]=dl+dr if op=='*' else max(dl,dr);known.add(n);producers[n]=(l,r);M+=op=='*'
  live=set();todo=[vv['output']]
  while todo:
   x=todo.pop()
   if type(x)is int or x in live:continue
   live.add(x);todo.extend(producers.get(x,()))
  need(live==set(producers)|set(vv['ports'])|set(constants),'every row port numeral live')
  ledgers[name]={'M':M,'A':len(producers)-M,'total':len(producers),'degree_upper':degree[vv['output']]}
  need(all(vv['ledger'][k]==ledgers[name][k] for k in ['M','A','total']),'exact ledger')
  for prime in [1000000007,1000000009]:
   need(D%prime!=0 and all(z%prime for z in pivots),'nonzero scale and pivots in sample field')
   def op(kind,l,r):return (l*r if kind=='*' else l+r if kind=='+' else l-r)%prime
   for i,row in enumerate(table):
    x=[i-17,3];y=[-7,2*i+1]
    def act(v,m):return [v[0]*m[0]+v[1]*m[2],v[0]*m[1]+v[1]*m[3]]
    ports=dict(zip(STATE,x+y+act(x,row['K'])+act(y,row['G'])));ports.update(selector=nodes[i],n=0,next_n=0)
    env={k:z%prime for k,z in constants.items()};env.update(ports)
    need(rows_eval(vv['instructions'],env,op)[vv['output']]==0,'all tiles whole source modulo prime');modchecks+=1
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':PINS,'ledgers':ledgers,
  'determinant_nonzero_pivot_checks':len(pivots),'exact_coefficients':576,'closed_formula_divisions':divisions,
  'fixed_numeral_bindings':len(constants),'whole_source_modular_checks':modchecks,'full_synchronized_cut_terms':len(expected),
  'scope':'Exact fixed numerals, literal arrays and unrestricted residual identity; modular samples supplement proof. No predecessor code executed.'}
def main():
 q=argparse.ArgumentParser();q.add_argument('--root',type=Path,required=True);q.add_argument('--author-root',type=Path)
 g=q.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=q.parse_args();r=verify(a.root,a.author_root or a.root)
 if a.expect:need(exact(r,load(a.expect.read_bytes())),'exact receipt replay')
 else:
  with a.output.open('x') as out:out.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(r,sort_keys=True))
if __name__=='__main__':main()
