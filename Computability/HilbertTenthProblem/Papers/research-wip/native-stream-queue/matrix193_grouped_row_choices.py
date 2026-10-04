#!/usr/bin/env python3
"""Literal grouped nonnegative row-choice predicates; no predecessor execution."""
import argparse,collections,copy,hashlib,json,pathlib
from fractions import Fraction
PINS={
'matrix193_synchronized_rows.py':'da55246efc8047b6b3f188579cf6c71bbabb067def3fe04ac47ba61b56517e52',
'matrix193_synchronized_rows.json':'9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233',
'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
'matrix193_countdown_rows.py':'5a1d373933f43b9f94dc54cf276aaa865fc6c82a1a25082842d8d4690e668577',
'matrix193_countdown_rows.json':'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0',
'matrix193_countdown_rows.md':'93363ca2f21949e2c7fa6d2bd4052b2219ec06fe4c2d52ba317fc19a229c5361'}
PORTS=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def load(b):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda s:(_ for _ in ()).throw(ValueError(s)))
class Source:
 def __init__(self):self.rows=[];self.memo={}
 def op(self,op,a,b):
  if type(a)is int and type(b)is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  if op=='+' and a==0:return b
  if op in ['+','-'] and b==0:return a
  if op in ['+','*'] and repr(a)>repr(b):a,b=b,a
  key=(op,a,b)
  if key not in self.memo:
   n='r'+str(len(self.rows));self.rows.append([n,op,a,b]);self.memo[key]=n
  return self.memo[key]
 def sum(self,seq):
  z=seq[0]
  for x in seq[1:]:z=self.op('+',z,x)
  return z
 def product(self,seq):
  z=seq[0]
  for x in seq[1:]:z=self.op('*',z,x)
  return z
 def lane(self,offset,matrix):
  residuals=[]
  for j in [0,1]:
   pred=self.op('+',self.op('*',PORTS[offset],matrix[j]),self.op('*',PORTS[offset+1],matrix[j+2]))
   residuals.append(self.op('-',PORTS[4+offset+j],pred))
  norm=self.sum([self.op('*',r,r) for r in residuals])
  return residuals,norm

def build_sync(table):
 e=Source();groups=collections.OrderedDict();lanes=[]
 for row in table:
  key=tuple(row['K'])
  if key not in groups:
   residual,a=e.lane(0,row['K']);groups[key]={'K':row['K'],'upper_residuals':residual,'upper_norm':a,'members':[]}
  residual,b=e.lane(2,row['G'])
  member={'tile_id':row['tile_id'],'G':row['G'],'lower_residuals':residual,'lower_norm':b}
  groups[key]['members'].append(member);lanes.append(member)
 for g in groups.values():
  g['lower_product']=e.product([m['lower_norm'] for m in g['members']])
  g['factor']=e.op('+',g['upper_norm'],g['lower_product'])
 split=len(e.rows);out=e.product([g['factor'] for g in groups.values()])
 return {'ports':PORTS,'instructions':e.rows,'groups':list(groups.values()),'product_start':split,'output':out,'exact_degree':192,'selector_witnesses':0}
def add(a,b,sign=1):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def mul(a,b):
 out={}
 for p,u in a.items():
  for q,v in b.items():
   k=tuple(x+y for x,y in zip(p,q));out[k]=out.get(k,0)+u*v
 return {k:v for k,v in out.items() if v}
def environment(ports):
 zero=(0,)*len(ports)
 return zero,{x:{tuple(int(i==j) for j in range(len(ports))):1} for i,x in enumerate(ports)}
def atom(x,v,zero):return {zero:x} if type(x)is int and x else {} if type(x)is int else v[x]
def polyop(op,a,b):return mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
def independent_residual(offset,j,m,v,z):
 return add(v[PORTS[4+offset+j]],add(mul({z:m[j]},v[PORTS[offset]]),mul({z:m[j+2]},v[PORTS[offset+1]])),-1)
def audit_sync(p,table):
 z,v=environment(PORTS)
 for name,op,a,b in p['instructions'][:p['product_start']]:v[name]=polyop(op,atom(a,v,z),atom(b,v,z))
 count=0;terms=0
 for g in p['groups']:
  rs=[independent_residual(0,j,g['K'],v,z) for j in [0,1]]
  for wire,r in zip(g['upper_residuals'],rs):need(v[wire]==r,'upper affine residual');count+=1
  a=add(mul(rs[0],rs[0]),mul(rs[1],rs[1]));need(v[g['upper_norm']]==a,'upper norm')
  product={z:1}
  for m in g['members']:
   rs=[independent_residual(2,j,m['G'],v,z) for j in [0,1]]
   for wire,r in zip(m['lower_residuals'],rs):need(v[wire]==r,'lower affine residual');count+=1
   b=add(mul(rs[0],rs[0]),mul(rs[1],rs[1]));need(v[m['lower_norm']]==b,'lower norm')
   product=mul(product,b)
  need(v[g['lower_product']]==product,'lower product')
  expected=add(a,product);need(v[g['factor']]==expected,'complete group factor');terms+=len(expected)
 factors=[g['factor'] for g in p['groups']];acc=factors[0]
 for (name,op,a,b),f in zip(p['instructions'][p['product_start']:],factors[1:]):
  need(op=='*' and {a,b}=={acc,f},'full outer finalizer');acc=name
 need(acc==p['output'] and len(p['instructions'])-p['product_start']==71,'all72 factors')
 actual=[(tuple(g['K']),m['tile_id'],tuple(m['G'])) for g in p['groups'] for m in g['members']]
 expected=[(tuple(r['K']),r['tile_id'],tuple(r['G'])) for r in table]
 need(sorted(actual)==sorted(expected) and len(actual)==96,'exact branch partition')
 scalar=[]
 for j in range(4):
  vals=[tuple(r['K' if j<2 else 'G'][k] for k in [j%2,j%2+2]) for r in table]
  scalar.append(len(set(vals)))
 need(scalar==[72,72,96,96],'scalar duplicate inventory')
 need(all((r['K'][0],r['K'][2])==(s['K'][0],s['K'][2]) if r['K']==s['K'] else (r['K'][0],r['K'][2])!=(s['K'][0],s['K'][2]) for r in table for s in table),'upper0 group coincidence')
 need(all((r['K'][1],r['K'][3])==(s['K'][1],s['K'][3]) if r['K']==s['K'] else (r['K'][1],r['K'][3])!=(s['K'][1],s['K'][3]) for r in table for s in table),'upper1 group coincidence')
 return {'independent_affine_residuals':count,'complete_group_factor_coefficients':terms,'groups':72,'branches':96,'distinct_scalar_residuals':scalar,'group_size_histogram':dict(sorted(collections.Counter(len(g['members']) for g in p['groups']).items()))}
def ledger(p):
 rows=p['instructions'];known=set(p['ports']);producers={}
 for n,op,a,b in rows:
  need(n not in known and op in ['+','-','*'],'source format')
  need(all(type(x)is int or x in known for x in [a,b]),'source closure');known.add(n);producers[n]=[a,b]
 todo=[p['output']];live=set()
 while todo:
  x=todo.pop()
  if type(x)is int or x in live:continue
  live.add(x);todo+=producers.get(x,[])
 need(set(producers)<=live,'all computed rows live')
 m=sum(r[1]=='*' for r in rows)
 return {'M':m,'A':len(rows)-m,'total':len(rows),'all_computed_rows_live':True}
def extend_countdown(sync,parent,old_sync):
 p={'ports':list(parent['ports']),'instructions':copy.deepcopy(sync['instructions']),'output':None,'exact_degree':194,'selector_witnesses':0}
 rename={old_sync['output']:sync['output']}
 def ref(x):return rename.get(x,x)
 for oldname,op,a,b in parent['instructions'][len(old_sync['instructions']):]:
  name='r'+str(len(p['instructions']));p['instructions'].append([name,op,ref(a),ref(b)]);rename[oldname]=name
 p['output']=rename[parent['output']];p['parent_tile_output']=sync['output']
 p['loader_factor']=ref(parent['loader_factor']);p['tile_factor']=ref(parent['tile_factor'])
 p['loader_residuals']=[ref(x) for x in parent['loader_residuals']]
 return p
def formal_countdown(p,start):
 ports=PORTS+['n','next_n','P'];z,v=environment(ports);v[p['parent_tile_output']]=v['P']
 for name,op,a,b in p['instructions'][start:]:v[name]=polyop(op,atom(a,v,z),atom(b,v,z))
 B=[52891,-29036,94920,-52109]
 rs=[add(v['next_x0'],v['x0'],-1),add(v['next_x1'],v['x1'],-1)]
 for j in [0,1]:rs.append(add(v[PORTS[6+j]],add(mul({z:B[j]},v['y0']),mul({z:B[j+2]},v['y1'])),-1))
 rs.append(add(add(v['n'],v['next_n'],-1),{z:1},-1))
 load={}
 for r in rs:load=add(load,mul(r,r))
 tile=add(add(v['P'],mul(v['n'],v['n'])),mul(v['next_n'],v['next_n']))
 need(v[p['loader_factor']]==load and v[p['tile_factor']]==tile,'loader and counter guard')
 expected=mul(load,tile);need(v[p['output']]==expected,'complete countdown wrapper')
 return len(expected)
def degree_line(p):
 z=(0,);v={x:{(1,):1} if x=='next_y0' else {} for x in p['ports']};degrees={x:1 for x in p['ports']}
 for name,op,a,b in p['instructions']:
  v[name]=polyop(op,atom(a,v,z),atom(b,v,z))
  da=0 if type(a)is int else degrees[a];db=0 if type(b)is int else degrees[b]
  degrees[name]=da+db if op=='*' else max(da,db)
 expected={(192,):1} if len(p['ports'])==8 else {(194,):1,(192,):1}
 need(v[p['output']]==expected,'exact full degree line')
 need(degrees[p['output']]==p['exact_degree'],'source degree upper')
 return [[e[0],c] for e,c in sorted(expected.items())]
def evaluate(p,values):
 v=dict(zip(p['ports'],values))
 for n,op,a,b in p['instructions']:
  a=a if type(a)is int else v[a];b=b if type(b)is int else v[b]
  v[n]=a*b if op=='*' else a-b if op=='-' else a+b
 return v[p['output']]
def row(v,m):return [v[0]*m[0]+v[1]*m[2],v[0]*m[1]+v[1]*m[3]]
def relation(table,v,countdown=False):
 x,y,nx,ny=v[:2],v[2:4],v[4:6],v[6:8]
 tile=any(row(x,t['K'])==nx and row(y,t['G'])==ny for t in table)
 if not countdown:return tile
 n,nn=v[8:10]
 return (tile and n==0 and nn==0) or (nx==x and ny==row(y,[52891,-29036,94920,-52109]) and nn==n-1)
def verify(root):
 data={}
 for name,h in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==h,'pin '+name);data[name]=b
 old=load(data['matrix193_synchronized_rows.json']);count=load(data['matrix193_countdown_rows.json'])
 need(old['source_sha256']==PINS['matrix193_synchronized_rows.py'] and count['source_sha256']==PINS['matrix193_countdown_rows.py'],'parent self-hashes')
 table=old['transition_table'];need(count['transitions']['tiles']==table,'same actual transition table')
 need(count['packet']['instructions'][:len(old['packet']['instructions'])]==old['packet']['instructions'],'literal retained parent prefix')
 need(len(count['packet']['instructions'])-len(old['packet']['instructions'])==26,'literal26-row countdown extension')
 sync=build_sync(table);checks=audit_sync(sync,table);sync['ledger']=ledger(sync)
 need(sync['ledger']['M']==1103 and sync['ledger']['A']==912 and sync['ledger']['total']==2015,'sync cost')
 down=extend_countdown(sync,count['packet'],old['packet']);down['ledger']=ledger(down)
 need(down['ledger']['M']==1115 and down['ledger']['A']==926 and down['ledger']['total']==2041,'countdown cost')
 checks['wrapper_coefficients']=formal_countdown(down,len(sync['instructions']))
 sync['degree_certificate_next_y0']=degree_line(sync);down['degree_certificate_next_y0']=degree_line(down)
 cases=0
 for t in table:
  x=[-2,3];y=[5,-7];v=x+y+row(x,t['K'])+row(y,t['G'])
  need(evaluate(sync,v)==0 and relation(table,v),'tile source zero')
  need(evaluate(down,v+[0,0])==0 and relation(table,v+[0,0],True),'guarded tile source zero');cases+=2
 for n in [-2,0,1,Fraction(3,2)]:
  x=[-2,3];y=[5,-7];v=x+y+x+row(y,[52891,-29036,94920,-52109])+[n,n-1]
  need(evaluate(down,v)==0 and relation(table,v,True),'loader source zero');cases+=1
 for i in range(16):
  v=[Fraction(((i+3)*(j+5))%13-6,1+(i%3)) for j in range(10)]
  need((evaluate(sync,v[:8])==0)==relation(table,v[:8]),'arbitrary sync equivalence')
  need((evaluate(down,v)==0)==relation(table,v,True),'arbitrary countdown equivalence');cases+=2
 checks['whole_signed_rational_source_checks']=cases
 return {'status':'PASS_EXACT_LOCAL_ZERO_RELATIONS','scope':'Two complete emitted local predicates with same signed real zero sets; no all-value equality with parent, no fixed-arity unbounded-history certificate','pins':PINS,'source_sha256':sha(pathlib.Path(__file__).read_bytes()),'predecessor_code_executed':False,'transition_table':table,'variants':{'synchronized':sync,'countdown':down},'initial_state':count['initial_state'],'endpoint':count['packet']['endpoint'],'checks':checks,'savings':{'synchronized':{'M':0,'A':24,'total':24},'countdown':{'M':0,'A':24,'total':24}},'fixed_duration_bounds':{'countdown':{'h_coefficient':2042,'constant':7,'signed_witnesses_per_step':5,'degree_upper':194,'input_loader_gates':0},'synchronized_supplied_target':{'d_coefficient':2016,'constant':5,'signed_witnesses_per_step':4,'degree_upper':192}},'new_universal_Diophantine_bound':False,'unbounded_history_packing_paid':False}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=pathlib.Path);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=pathlib.Path);g.add_argument('--expect',type=pathlib.Path);a=p.parse_args();r=verify(a.root.resolve());text=json.dumps(r,indent=2,sort_keys=True)+'\n'
 need(json.dumps(json.loads(text),indent=2,sort_keys=True)+'\n'==text,'typed JSON round trip')
 if a.expect:need(a.expect.read_text()==text,'exact receipt replay')
 else:
  with a.output.open('x') as f:f.write(text)
 print(json.dumps({'status':r['status'],'ledgers':{k:v['ledger'] for k,v in r['variants'].items()},'checks':r['checks']}))
if __name__=='__main__':main()
