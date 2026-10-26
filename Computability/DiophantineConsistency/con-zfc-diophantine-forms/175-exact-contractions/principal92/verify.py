#!/usr/bin/env python3
"""Full portable finite audit. Does not import the circuit producer or searches."""
from collections import Counter
from pathlib import Path
import argparse,copy,hashlib,json,random,re
import audit_core
ROOT=Path(__file__).resolve().parent
MOD=1000003
def require(ok,msg):
 if not ok:raise ValueError(msg)
def sparse(ts):return {tuple(m):c for c,m in ts}
def plus(p,q,a=1):
 r=dict(p)
 for m,c in q.items():
  z=r.get(m,0)+a*c
  if z:r[m]=z
  else:r.pop(m,None)
 return r
def times(p,q):
 r=Counter()
 for a,c in p.items():
  for b,d in q.items():r[tuple(sorted(a+b))]+=c*d
 return {m:c for m,c in r.items() if c}
def substitute(p,v,f):
 r={};powers={0:{():1},1:f}
 for mon,c in p.items():
  k=mon.count(v)
  for j in range(2,k+1):
   if j not in powers:powers[j]=times(powers[j-1],f)
  rest=tuple(u for u in mon if u!=v)
  r=plus(r,times({rest:c},powers[k]))
 return r
def check_bridge(raw220,source191,bridge):
 require(hashlib.sha256(raw220).hexdigest()==bridge['source_sha256'],'220 source binding')
 source220=json.loads(raw220);n=len(source220['variables']);rows={i:sparse(r['terms']) for i,r in enumerate(source220['residuals'])};gone=set()
 for step in bridge['steps']:
  i,v,a=step['row'],step['variable'],step['coefficient'];require(i in rows and v not in gone and a in (-1,1),'bridge pivot')
  r=rows[i];require(r.get((v,))==a and all(v not in mon for mon in r if mon!=(v,)),'bridge unit slope')
  f={mon:-a*c for mon,c in r.items() if mon!=(v,)};require(f==sparse(step['restoration']),'bridge restoration')
  del rows[i];gone.add(v)
  rows={j:substitute(q,v,f) for j,q in rows.items()}
 require(len(gone)==29 and len(rows)==128,'bridge dimensions')
 require([{'source_row':i,'terms':[[c,list(mon)] for mon,c in sorted(p.items())]} for i,p in sorted(rows.items())]==bridge['rows'],'bridge emitted rows')
 keep=[v for v in range(n) if v not in gone];ren={v:i for i,v in enumerate(keep)}
 require(source191['variables']==[source220['variables'][v] for v in keep],'191 source coordinates')
 require(len(source191['residuals'])==len(rows),'191 row count')
 for emitted,(i,p) in zip(source191['residuals'],sorted(rows.items())):
  expected={tuple(ren[v] for v in mon):c for mon,c in p.items()}
  require(sparse(emitted['terms'])==expected,'191 exact coefficients')
 return {'source220_variables':n,'source191_variables':len(keep),'unit_projections':len(gone),'retained_residuals':len(rows)}

def check_circuit(source,cert,circuit):
 require(circuit['schema']=='ordinary-integer-arithmetic-circuit-v1' and circuit['domain']=='unrestricted integers','circuit domain')
 free=cert['free_source_variables'];defs={s['variable']:sparse(s['restoration_source_terms']) for s in cert['steps']}
 require(circuit['input_count']==len(free)==92 and circuit['input_source_coordinates']==free,'circuit inputs')
 require(circuit['source_sha256']==cert['source_sha256'],'circuit source')
 # Intern exact expression tuples to prove structural equality. No numerical
 # hash equality is used for this algebraic comparison.
 tree={};seq=[]
 def intern(key):
  if key in tree:return tree[key]
  k=len(seq);tree[key]=k;seq.append(key);return k
 zero=intern(('const',0));one=intern(('const',1))
 def op(name,a,b):
  if name=='add':
   if a==zero:return b
   if b==zero:return a
  if name=='mul':
   if a==zero or b==zero:return zero
   if a==one:return b
   if b==one:return a
  if name in ('add','mul') and a>b:a,b=b,a
  return intern((name,a,b))
 actual=[]
 for i,node in enumerate(circuit['nodes']):
  require(type(node)is list and node,'node shape');kind=node[0]
  if kind=='const':require(len(node)==2 and type(node[1])is int,'literal');value=intern(('const',node[1]))
  elif kind=='input':require(len(node)==2 and type(node[1])is int and 0<=node[1]<92,'input index');value=intern(('input',node[1]))
  else:
   require(kind in ('add','mul','sub') and len(node)==3,'ordinary binary operation')
   require(all(type(v)is int and 0<=v<i for v in node[1:]),'acyclic binary graph');value=op(kind,actual[node[1]],actual[node[2]])
  actual.append(value)
 memo={v:intern(('input',i)) for i,v in enumerate(free)}
 def polynomial(ts):
  z=zero
  for c,mon in ts:
   term=intern(('const',c))
   for v in mon:term=op('mul',term,var(v))
   z=op('add',z,term)
  return z
 def var(v):
  if v not in memo:memo[v]=polynomial([[c,list(mon)] for mon,c in sorted(defs[v].items())])
  return memo[v]
 expected=[polynomial(source['residuals'][i]['terms']) for i in cert['retained_source_rows']]
 outs=circuit['residual_outputs'];require(len(outs)==29 and all(type(i)is int and 0<=i<len(actual) for i in outs),'residual outputs')
 require([actual[i] for i in outs]==expected,'circuit residual identities')
 total=zero
 for r in expected:total=op('add',total,op('mul',r,r))
 output=circuit['output'];require(type(output)is int and 0<=output<len(actual) and actual[output]==total,'circuit final polynomial')
 live=set();stack=[output]
 while stack:
  i=stack.pop()
  if i in live:continue
  live.add(i)
  if circuit['nodes'][i][0] in ('add','mul','sub'):stack.extend(circuit['nodes'][i][1:])
 require(live==set(range(len(actual))),'dead emitted node')
 return {'nodes':len(actual),'binary_arithmetic_gates':sum(n[0] in ('add','mul','sub') for n in circuit['nodes']),'largest_literal_integer':max(abs(n[1]) for n in circuit['nodes'] if n[0]=='const')}

def derivative_witness(circuit):
 for seed in range(10):
  rng=random.Random(923000+seed);point=[rng.randrange(1,1001) for _ in range(92)];values=[];grads=[]
  for node in circuit['nodes']:
   kind=node[0]
   if kind=='const':value=node[1]%MOD;gradient=[0]*92
   elif kind=='input':value=point[node[1]];gradient=[0]*92;gradient[node[1]]=1
   else:
    a,b=node[1:];av,bv=values[a],values[b];ag,bg=grads[a],grads[b]
    if kind=='add':value=(av+bv)%MOD;gradient=[(x+y)%MOD for x,y in zip(ag,bg)]
    elif kind=='sub':value=(av-bv)%MOD;gradient=[(x-y)%MOD for x,y in zip(ag,bg)]
    else:value=av*bv%MOD;gradient=[(x*bv+y*av)%MOD for x,y in zip(ag,bg)]
   values.append(value);grads.append(gradient)
  out=grads[circuit['output']]
  if all(out):return {'modulus':MOD,'point':point,'partial_derivative_residues':out,'all_92_coordinates_occur':True}
 raise ValueError('liveness witness not established')

def height_bound(source,cert):
 defs={s['variable']:sparse(s['restoration_source_terms']) for s in cert['steps']};memo={v:1 for v in cert['free_source_variables']}
 def upper_poly(p):
  total=0
  for mon,c in p.items():
   a=abs(c)
   for v in mon:a*=upper(v)
   total+=a
  return total
 def upper(v):
  if v not in memo:memo[v]=upper_poly(defs[v])
  return memo[v]
 rr=[upper_poly(sparse(source['residuals'][i]['terms'])) for i in cert['retained_source_rows']];total=sum(a*a for a in rr)
 return {'coefficient_height_strict_upper_bound_power_of_two':total.bit_length(),'max_residual_l1_bound_bitlength':max(a.bit_length() for a in rr),'method':'triangle inequality and multiplicativity bound for coefficient l1 norm','expanded_exact_height':'not computed','expanded_exact_support':'not computed'}

def check_printed(source,cert,receipt):
 def parse_file(path,lhs):
  text=path.read_text();pattern=r'\\begin\{align\*\}\s*'+lhs+r'_\{(\d+)\}\s*&=\{\}\s*(.*?)\s*\\end\{align\*\}'
  result={}
  for i,body in re.findall(pattern,text,re.S):
   body=body.replace('\\\\','').replace('&{}','');body=''.join(body.split());poly={}
   for term in re.findall(r'[+-]?[^+-]+',body):
    sign=-1 if term.startswith('-') else 1;term=term.lstrip('+-');match=re.match(r'\d+',term);c=int(match.group()) if match else 1
    if match:term=term[len(match.group()):]
    mon=[];pos=0
    while pos<len(term):
     m=re.match(r'y_\{(\d+)\}(?:\^\{(\d+)\})?',term[pos:]);require(m is not None,'unparsed TeX factor');mon.extend([int(m.group(1))]*int(m.group(2) or 1));pos+=len(m.group())
    key=tuple(sorted(mon));poly[key]=poly.get(key,0)+sign*c
   require(int(i) not in result,'duplicate printed left side');result[int(i)]={mon:c for mon,c in poly.items() if c}
  return result
 p=ROOT/'specification';rr=parse_file(p/'source191_residuals.tex','R');dd=parse_file(p/'definitions92.tex','y');defs={s['variable']:sparse(s['restoration_source_terms']) for s in cert['steps']}
 require(rr=={i:sparse(row['terms']) for i,row in enumerate(source['residuals'])},'printed source residual mismatch');require(dd==defs,'printed restoration mismatch')
 for name,expected in [('F',cert['free_source_variables']),('J',cert['retained_source_rows'])]:
  m=re.search(r'\\mathcal '+name+r'=\{\}&\((.*?)\)',(p/'index_lists.tex').read_text(),re.S);require(m is not None,'printed index header');require([int(x) for x in re.findall(r'\d+',m.group(1))]==expected,'printed indices')
 assign=[(int(y),int(x)) for y,x in re.findall(r'y_\{(\d+)\}=x_\{(\d+)\}',(p/'free_coordinates.tex').read_text())];require(assign==list(zip(cert['free_source_variables'],range(92))),'printed input assignment')
 return {'literal_source_residuals_parsed':len(rr),'literal_definitions_parsed':len(dd),'ordered_free_and_retained_lists_checked':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args()
 raw220=(ROOT/'sources/source220.json').read_bytes();raw191=(ROOT/'sources/source191.json').read_bytes();source=json.loads(raw191);bridge=json.loads((ROOT/'sources/bridge191.json').read_text());cert=json.loads((ROOT/'projection92.json').read_text());circuit=json.loads((ROOT/'circuit92.json').read_text())
 b=check_bridge(raw220,source,bridge);p=audit_core.check(source,cert,raw191);d=check_circuit(source,cert,circuit);l=derivative_witness(circuit);h=height_bound(source,cert);printed=check_printed(source,cert,p)
 controls=[]
 for label,change in [('wrong_restoration',lambda c:c['steps'][0]['restoration_source_terms'][0].__setitem__(0,2*c['steps'][0]['restoration_source_terms'][0][0])),('dropped_residual',lambda c:c['retained_source_rows'].pop())]:
  broken=copy.deepcopy(cert);change(broken)
  try:audit_core.check(source,broken,raw191)
  except ValueError:controls.append(label)
  else:raise ValueError('accepted '+label)
 broken=copy.deepcopy(circuit);i=next(i for i,node in enumerate(broken['nodes']) if node[0]=='add');broken['nodes'][i][0]='mul'
 try:check_circuit(source,cert,broken)
 except ValueError:controls.append('changed_binary_gate')
 else:raise ValueError('accepted wrong binary gate')
 receipt={'bridge220_to191':b,'projection191_to92':p,'literal_circuit':d,'occurrence_witness':l,'coefficient_bound':h,'printed_specification':printed,'negative_controls_rejected':controls,'scope':'finite exact polynomial proofs; inherited C222/ZF/ZFC calibration remains identified mathematical dependency'}
 if a.receipt:a.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'variables':p['variables'],'residuals':p['residuals'],'exact_degree':p['exact_degree'],**d,**h,'all_variables_occur':l['all_92_coordinates_occur'],'negative_controls_rejected':controls},sort_keys=True))
if __name__=='__main__':main()
