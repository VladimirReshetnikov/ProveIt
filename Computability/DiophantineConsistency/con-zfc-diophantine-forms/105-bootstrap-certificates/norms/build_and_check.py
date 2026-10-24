#!/usr/bin/env python3
"""Build exact norm rewrites and verify universal polynomial identities.

Standard library only. Authored code is confined to this packet; retained
source modules are imported from upstream without changing their files.
"""
from pathlib import Path
import copy, gzip, hashlib, importlib.util, json, sys
from collections import Counter
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream/rootfusion'))
import build_equations as parent
import build_reanchored as reanchored
sys.path.insert(0,str(HERE/'upstream'))
from exact_polynomial import Ring
from compact_norms import cleared_norm5 as old5
from norms import cleared_norm3, cleared_norm4, cleared_norm5

def need(ok,msg):
 if not ok: raise ValueError(msg)
def write(path,obj):
 path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def old3(x,a,b,C,d):
 z=x*x;s=a+b;T=d*d*a*b;R=d*C;J=d*(z-s)-C
 H=J*J-4*(T+R*s)
 return H*H-64*T*R*z

def old4(x,a,b,c,C,d):
 x2=x*x;d2=d*d
 q0=d*(x2+c-a-b)-C;q1=-2*d*x
 A0=q0*q0+c*q1*q1-4*(d2*a*b+d*C*(a+b))
 A1=2*q0*q1;z=64*d2*d*a*b*C
 f0=A0*A0+c*A1*A1-z*(x2+c)
 f1=2*A0*A1+2*z*x
 return f0*f0-c*f1*f1

def free_graph(fn,names):
 d=parent.DAG(names);v=[d.leaf('variable',n) for n in names]
 return parent.export('free_norm',d,fn(*v),{}, {})

def generic():
 results=[]
 for n,old,new in [(3,old3,cleared_norm3),(4,old4,cleared_norm4),(5,old5,cleared_norm5)]:
  names=['x','a','b']+(['c'] if n>=4 else [])+(['d'] if n>=5 else [])+['C','delta']
  r=Ring(names);v=[r.var(s) for s in names]
  a,b=old(*v),new(*v)
  need(a.terms==b.terms,'all generic coefficients equal')
  results.append({'roots':n,'monomials':len(a.terms),'old_operations':free_graph(old,names)['operations'],
                  'new_operations':free_graph(new,names)['operations'],'all_coefficients_equal':True,
                  'valid_at_zero_denominator':True})
 return results

def term_at(packet,idx,cuts,pool):
 memo={}
 def intern(t):
  if t not in pool:pool[t]=len(pool)
  return pool[t]
 def go(i):
  if i in cuts:return intern(('cut',cuts[i]))
  if i in memo:return memo[i]
  row=packet['nodes'][i]
  if row[0] in ('add','sub','mul'):
   x,y=go(row[1]),go(row[2])
   if row[0] in ('add','mul') and x>y:x,y=y,x
   t=(row[0],x,y)
  else:t=tuple(row)
  memo[i]=intern(t);return memo[i]
 return go(idx)

def cut_check(old,new,registers):
 pool={}
 for s in registers:
  need(term_at(old,old['named_registers'][s],{},pool)==term_at(new,new['named_registers'][s],{},pool),s+' whole prefix identity')
 for packet,fn in [(old,old5),(new,cleared_norm5)]:
  names=['x','a','b','c','d','C','delta'];p=free_graph(fn,names)
  cuts={packet['named_registers'][s]:n for s,n in zip(registers,names)}
  gcuts={i:row[1] for i,row in enumerate(p['nodes']) if row[0]=='variable'}
  pool={}
  need(term_at(packet,packet['output'],cuts,pool)==term_at(p,p['output'],gcuts,pool),'whole literal norm substitution')
 return {'prefix_cut_registers':registers,'prefixes_identical':True,'both_generic_norm_substitutions_checked':True}

def integer_forms():
 cases=[('norm13_degree1408',lambda:parent.make13(False)),('norm13_degree1392',lambda:parent.make13(True)),
        ('norm13_crt_degree1088',parent.make13crt),('norm13_crt_guard_degree1072',reanchored.build)]
 out=[]
 for basename,builder in cases:
  parent.cleared_norm5=old5;reanchored.cleared_norm5=old5
  old=builder();stored=json.loads((HERE/'upstream/rootfusion'/f'{basename}.json').read_text())
  for field in ['nodes','output','variables','operations']:need(old[field]==stored[field],basename+' retained literal '+field)
  parent.cleared_norm5=cleared_norm5;reanchored.cleared_norm5=cleared_norm5
  new=builder()
  regs=['center','scaled_Df','scaled_Dtau','scaled_Dmain' if 'crt' in basename else 'Dmain','scaled_Ag','scaled_Cy','delta']
  cert=cut_check(old,new,regs)
  new['name']=basename+'_short_norm';new['coefficient_binding']='../upstream/rootfusion/coefficients/BINDING.json'
  new['semantic_proof']='../PROOF.md; unchanged parent ordinary source calibration'
  new['parent_literal']=f'../upstream/rootfusion/{basename}.json';new['proof_status']='Exact entire-polynomial identity; inherited ordinary source calibration unchanged.'
  write(HERE/'equations'/f'{new["name"]}.json',new)
  out.append({'name':new['name'],'domain':new['domain'],'variables':new['variable_count'],'degree':new['exact_degree'],
              'parent_operations':old['operations'],'operations':new['operations'],'whole_polynomial_equality':cert})
 parent.cleared_norm5=old5;reanchored.cleared_norm5=old5
 return out

def positive11():
 p=json.loads((HERE/'upstream/positive11_111.json').read_text())
 prefix=p['source'][:next(i for i,r in enumerate(p['source']) if r[0]=='z2')]
 tail=[['z2','*','Zbar','Zbar'],['np_a_b','-','A','Bf'],['np_sum','+','z2','np_a_b'],
 ['np_dsum','*','delta','np_sum'],['np_G','-','np_dsum','Cnum'],['np_d2','*','delta','delta'],
 ['np_d2a','*','np_d2','A'],['np_U','*','np_d2a','z2'],['np_db','*','delta','Bf'],
 ['np_V','*','np_db','Cnum'],['np_G2','*','np_G','np_G'],['np_UV','-','np_U','np_V'],
 ['np_4UV','*',4,'np_UV'],['np_H','+','np_G2','np_4UV'],['np_H2','*','np_H','np_H'],
 ['np_UG2','*','np_U','np_G2'],['np_tail','*',16,'np_UG2'],['N8','-','np_H2','np_tail']]
 final=p['source'][-3:];q=copy.deepcopy(p);q['source']=prefix+tail+final
 q.update(name='positive11_degree211_short_norm',operations=len(q['source']),system_operations=len(q['source'])-3,
          operation_breakdown=dict(Counter(row[1] for row in q['source'])),
          coefficient_binding={'file':'../upstream/positive11/coefficients/ACTIVE_BINDING.json','ports':{'beta':'beta','K0':'K0','MC':'MC','MF':'MF'}},
          provenance={'change':'Exact cleared three-root norm rewrite; every prefix and finalizer row is unchanged.'},
          proof_status='Exact entire-polynomial identity; inherited ordinary source calibration unchanged.')
 r=Ring(['x','a','b','C','delta']);values={n:r.var(s) for n,s in zip(['Zbar','A','Bf','Cnum','delta'],r.names)}
 def run(rows):
  v=dict(values)
  for n,op,a,b in rows:
   x=a if isinstance(a,int) else v[a];y=b if isinstance(b,int) else v[b]
   v[n]=x+y if op=='+' else x-y if op=='-' else x*y
  return v['N8']
 old_tail=p['source'][len(prefix):-3]
 need(run(old_tail).terms==run(tail).terms,'positive11 complete generic tail identity')
 need(q['operations']==110,'positive11 operation count')
 binding=json.loads((HERE/'upstream/positive11/coefficients/ACTIVE_BINDING.json').read_text())
 for name,rec in binding['ports'].items():
  packed=(HERE/'upstream/positive11/coefficients'/rec['gzip_payload']).read_bytes();raw=gzip.decompress(packed)
  need(hashlib.sha256(packed).hexdigest()==rec['gzip_sha256'],'positive fixed gzip '+name)
  need(hashlib.sha256(raw).hexdigest()==rec['sha256'],'positive fixed bytes '+name)
  need(int.from_bytes(raw,'little').bit_length()==rec['bits'],'positive fixed bits '+name)
 inputs=set(q['witnesses']+q['fixed_numerals']);available=set(inputs);parents={}
 for name,op,a,b in q['source']:
  need(name not in available,'new register');need(op in ['+','-','*'],'binary polynomial opcode')
  need(all(type(v)is int or v in available for v in [a,b]),'topological order')
  parents[name]=[v for v in [a,b] if type(v)is str];available.add(name)
 live=set();todo=[q['output']]
 while todo:
  z=todo.pop()
  if z not in live:live.add(z);todo.extend(parents.get(z,[]))
 need(live==available,'all positive gates and inputs live')
 write(HERE/'equations/positive11_degree211_short_norm.json',q)
 return {'name':q['name'],'domain':q['domain'],'variables':11,'degree':211,'parent_operations':111,'operations':110,
         'unchanged_prefix_rows':len(prefix),'unchanged_finalizer_rows':3,'whole_tail_identity_checked':True}

def main():
 (HERE/'equations').mkdir(exist_ok=True)
 pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
 for rec in pins['retained_files']:
  target=HERE/rec['path']
  need(target.stat().st_size==rec['bytes'] and digest(target)==rec['sha256'],'retained source pin '+rec['path'])
 g=generic();f=integer_forms();f.append(positive11())
 coeff=parent.load_base_coefficients()
 need(set(coeff)==set(parent.BASE_PORTS),'all actual fixed coefficients available')
 result={'status':'PASS','python_optimization':sys.flags.optimize,'generic_norms':g,'equations':f,
         'fixed_integer_payloads_authenticated':True,'scope':'Exact polynomial identities and complete literal substitution; no semantic proof search.'}
 write(HERE/('CHECKS_OPTIMIZED.json' if sys.flags.optimize else 'CHECKS.json'),result)
 print(json.dumps({'status':'PASS','generic':g,'equations':[{k:x[k] for k in ['name','variables','degree','operations','parent_operations']} for x in f]},indent=2))
if __name__=='__main__':main()
