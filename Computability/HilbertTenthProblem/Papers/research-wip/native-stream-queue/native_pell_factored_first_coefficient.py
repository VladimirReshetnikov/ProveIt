#!/usr/bin/env python3
"""Pinned exact first-coefficient transfer: prescribed AND63 and four full clocks.
Historical sources are authenticated as bytes, never imported or executed.
"""
import argparse,copy,hashlib,json,random,tempfile,subprocess,sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'native_binary_masked_selection63.py':'fcff972928d234450901021b2fce5acf41e0c917ab8174ac67fee0b60df7c985',
'native_binary_masked_selection63.json':'18f0f6158aa1ef6da2a648f1eaef125d2cacbde7ed302be89044075ba875823d',
'native_binary_masked_selection63.md':'c2e08f2d9fdaaf2e17880d7a131254492afd7ef21b035985714734cbc158c53e',
'native_binary_positive_scale.py':'94842053d35207d73b4ac1890552b16d7576a017f957c0c97bd42ca5d5a5b81d',
'native_binary_positive_scale.json':'ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628',
'native_binary_positive_scale.md':'d958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97',
'three_mass_unbounded_interface.py':'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a',
'three_mass_unbounded_interface.json':'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
'three_mass_unbounded_interface.md':'d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45'}
VARIANTS=('and_prescribed','and_positive_scale','clock_incdec','clock_zero3','clock_nop','clock_positive3')
EXPECTED={'and_prescribed':(64,33,31,22,16,111,28),'and_positive_scale':(64,33,31,21,15,108,28),
'clock_incdec':(539,217,322,59,20,598,2344),'clock_zero3':(414,162,252,57,20,473,1192),
'clock_nop':(412,160,252,57,20,471,1192),'clock_positive3':(415,167,248,57,20,474,1192)}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def _receipt(root,stem):
 root=Path(root)
 for ext in ('.py','.json','.md'):
  n=stem+ext;need(sha((root/n).read_bytes())==PINS[n],'pinned dependency '+n)
 return json.loads((root/(stem+'.json')).read_text())

def _sos(source,comparisons):
 rows=copy.deepcopy(source)
 for i,(a,b) in enumerate(comparisons):rows.extend([[f'sos_res{i}','-',a,b],[f'sos_sq{i}','*',f'sos_res{i}',f'sos_res{i}']])
 out='sos_sq0'
 for i in range(1,len(comparisons)):
  n=f'sos_sum{i}';rows.append([n,'+',out,f'sos_sq{i}']);out=n
 return rows,out

def _ledger(rows,terminals,parameters,auxiliaries):
 need(type(rows)is list and type(parameters)is list and type(auxiliaries)is list,'exact source/interface containers')
 need(all(type(n)is str for n in parameters+auxiliaries),'exact coordinate names')
 free=set(parameters+auxiliaries);need(len(free)==len(parameters)+len(auxiliaries),'disjoint complete interface')
 seen=set(free);deps={};degrees={n:1 for n in free};counts=Counter()
 for row in rows:
  need(type(row)is list and len(row)==4,'exact four-item row');n,op,a,b=row
  need(type(n)is str and n not in seen and type(op)is str and op in ('+','-','*'),'fresh typed gate')
  need(all(type(v)is int or type(v)is str and v in seen for v in (a,b)),'exact closed operands')
  ds=[degrees[v] if type(v)is str else 0 for v in (a,b)];degrees[n]=sum(ds) if op=='*' else max(ds)
  seen.add(n);deps[n]=(a,b);counts['M' if op=='*' else 'A']+=1
 actual={v for row in rows for v in row[2:] if type(v)is str and v not in deps}
 actual.update(v for v in terminals if type(v)is str and v not in deps)
 need(actual==free,'exact entire free coordinate set')
 live=set();pending=list(terminals)
 while pending:
  n=pending.pop()
  if type(n)is int or n in free or n in live:continue
  need(n in deps,'defined terminal');live.add(n);pending.extend(deps[n])
 need(live==set(deps),'all emitted gates live')
 upper=max(degrees[v] if type(v)is str else 0 for v in terminals)
 return dict(operations=len(rows),M=counts['M'],A=counts['A'],positive_witnesses=len(auxiliaries),parameters=parameters[:],degree_upper_bound=upper,all_gates_live=True,free_coordinates=sorted(free))

def canonical_parent(root=None,variant='and_prescribed'):
 need(type(variant)is str and variant in VARIANTS,'exact selected variant')
 root=Path(__file__).resolve().parent if root is None else Path(root)
 if variant=='and_prescribed':
  j=_receipt(root,'native_binary_masked_selection63')['variants']['and64_prescribed']
  rows=j['source'];pairs=j['comparisons'];parameters=j['parameters'];aux=j['strictly_positive_auxiliaries']
  polynomial,out=_sos(rows,pairs);metadata={k:v for k,v in j.items() if k not in ('source','comparisons','parameters','strictly_positive_auxiliaries')}
  degree={'upper_bound':28,'exact_degree':28,'basis':'unchanged parent polynomial'}
 elif variant=='and_positive_scale':
  j=_receipt(root,'native_binary_positive_scale');e=j['example'];pairs=e['comparisons'];parameters=e['parameters'];aux=e['auxiliaries']
  polynomial=e['source'];out=e['output'];rows=polynomial[:len(polynomial)-(3*len(pairs)-1)]
  metadata={k:v for k,v in j.items() if k!='example'};degree={'upper_bound':28,'exact_degree':None,'basis':'parent claims upper bound only'}
 else:
  j=_receipt(root,'three_mass_unbounded_interface');e=next(f for f in j['fixtures'] if f['name']==variant[6:])
  polynomial=e['source'];out=e['output'];pairs=e['comparisons'];parameters=e['parameters'];aux=e['auxiliaries'];rows=polynomial[:len(polynomial)-(3*len(pairs)-1)]
  metadata={k:v for k,v in e.items() if k not in ('source','output','comparisons','parameters','auxiliaries')}
  degree={'upper_bound':e['ledger']['degree_upper_bound'],'exact_degree':None,'basis':'parent claims upper bound only'}
 need(exact(_sos(rows,pairs), (polynomial,out)),'entire literal parent SOS')
 c=_ledger(rows,[v for pair in pairs for v in pair],parameters,aux);p=_ledger(polynomial,[out],parameters,aux)
 expected=EXPECTED[variant];need((c['operations'],c['M'],c['A'],len(aux),len(pairs),p['operations'],p['degree_upper_bound'])==expected,'complete authenticated ledger')
 return copy.deepcopy(dict(variant=variant,source=rows,comparisons=pairs,polynomial_source=polynomial,output=out,parameters=parameters,auxiliaries=aux,
  domains={'parameters':'natural' if variant.startswith('clock_') else 'positive','auxiliaries':'positive'},certificate_ledger=c,polynomial_ledger=p,degree=degree,
  parent_metadata=metadata,parent_metadata_role='historical provenance only; not active register declarations',
  scope='Prescribed binary AND component' if variant.startswith('and_') else 'Fixed finite three-mass program, exact first-halt physical clock and raw natural input/output; no universal ordinary-input claim'))

def _rewrite_canonical(parent):
 p=copy.deepcopy(parent);prefix='native__' if p['variant'].startswith('clock_') else '';n=lambda v:prefix+v
 rows=p['source'];d={v:(op,a,b) for v,op,a,b in rows}
 need(d[n('UM')]==('*',n('wn2'),n('sn2')),'literal E=X*Y')
 need(d[n('ksn2')]==('*',n('k'),n('sn2')),'literal supplied k*Y; do not use ratio equality')
 expected={'UM2':('*',n('UM'),n('UM')),'scaled_norm_coefficient':('+',n('UM2'),n('wn2')),
 'ratio_product2':('*',n('ksn2'),n('ksn2')),'L9':('*',n('scaled_norm_coefficient'),n('ratio_product2'))}
 need(all(d[n(k)]==v for k,v in expected.items()),'exact private four-gate coefficient')
 for private,user in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
  need({v for v,op,a,b in rows if n(private) in (a,b)}=={n(user)},'unique private consumer')
  need(all(n(private) not in pair for pair in p['comparisons']),'private value is not comparison port')
 need(n('k') in p['auxiliaries'],'selected k is supplied positive coordinate')
 need(n('factored_first_base') not in d and n('factored_first_next') not in d,'fresh private names')
 removed={n(k) for k in expected};new=[]
 for row in rows:
  if row[0]==n('L9'):
   new.extend([[n('factored_first_base'),'*',n('UM'),n('ksn2')],[n('factored_first_next'),'+',n('factored_first_base'),n('k')],[n('L9'),'*',n('factored_first_base'),n('factored_first_next')]])
  elif row[0] not in removed:new.append(row)
 p['source']=new;p['polynomial_source'],p['output']=_sos(new,p['comparisons'])
 p['certificate_ledger']=_ledger(new,[v for pair in p['comparisons'] for v in pair],p['parameters'],p['auxiliaries'])
 p['polynomial_ledger']=_ledger(p['polynomial_source'],[p['output']],p['parameters'],p['auxiliaries'])
 for key in ('certificate_ledger','polynomial_ledger'):
  a=parent[key];b=p[key];need(b['operations']==a['operations']-1 and b['M']==a['M']-1 and b['A']==a['A'],'one fully paid multiplication removed')
  need(b['free_coordinates']==a['free_coordinates'] and b['degree_upper_bound']==a['degree_upper_bound'],'all input coordinates and upper degree preserved')
 p['transfer']={'exact_same_polynomial':True,'same_supplied_coordinates':True,'prefix':prefix,'actual_k_port':n('k'),
 'removed_private_registers':[n(k) for k in ('UM2','scaled_norm_coefficient','ratio_product2')],
 'new_private_registers':[n('factored_first_base'),n('factored_first_next')],
 'literal_identity':'((XY)^2+X)*(kY)^2 = (XY*kY)*(XY*kY+k)',
 'parent_source_sha256':sha(json.dumps(rows,separators=(',',':')).encode()),'comparison_indices_preserved':list(range(len(p['comparisons'])))}
 return p

def build(root=None,variant='and_prescribed'):return _rewrite_canonical(canonical_parent(root,variant))
def rewrite(root,variant,supplied):
 expected=canonical_parent(root,variant);need(exact(supplied,expected),'entire exact canonical parent required');return _rewrite_canonical(expected)
def checked(root,packet):
 need(type(packet)is dict and type(packet.get('variant'))is str,'exact packet with variant')
 expected=build(root,packet['variant']);need(exact(packet,expected),'entire canonical child required');return expected
def polynomial_source(root,packet):return checked(root,packet)['polynomial_source']
def _execute(rows,values):
 env=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  env[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return env
def evaluate(root,packet,values,*,signed=False):
 need(type(signed)is bool,'exact signed Boolean');p=checked(root,packet)
 need(type(values)is dict and set(values)==set(p['parameters']+p['auxiliaries']),'complete exact input dictionary')
 need(all(type(n)is str and type(v)is int for n,v in values.items()),'exact integer values')
 if not signed:
  need(all(values[n]>0 for n in p['auxiliaries']),'positive auxiliaries')
  need(all(values[n]>=0 if p['domains']['parameters']=='natural' else values[n]>0 for n in p['parameters']),'inherited parameter domain')
 return _execute(p['polynomial_source'],values)[p['output']]

def _local_identity(parent,child):
 # Independently expand both actual cones in Q[X,Y,k].
 prefix=child['transfer']['prefix'];n=lambda v:prefix+v;zero=(0,0,0)
 def add(a,b,sign=1):
  out=a.copy()
  for m,v in b.items():out[m]=out.get(m,0)+sign*v
  return {m:v for m,v in out.items() if v}
 def mul(a,b):
  out={}
  for m,v in a.items():
   for k,w in b.items():
    e=tuple(x+y for x,y in zip(m,k));out[e]=out.get(e,0)+v*w
  return {m:v for m,v in out.items() if v}
 def run(rows):
  e={n('wn2'):{(1,0,0):1},n('sn2'):{(0,1,0):1},n('k'):{(0,0,1):1}}
  for dest,op,a,b in rows:
   if dest in e:continue
   if (type(a)is int or a in e) and (type(b)is int or b in e):
    a={zero:a} if type(a)is int else e[a];b={zero:b} if type(b)is int else e[b]
    e[dest]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return e[n('L9')]
 expected={(2,4,2):1,(1,2,2):1};need(run(parent['source'])==run(child['source'])==expected,'literal cone coefficient identity')
 return [[list(m),v] for m,v in sorted(expected.items())]

def _whole_identity(parent,child):
 prefix=child['transfer']['prefix'];L9=prefix+'L9';atoms={}
 def intern(a):
  if a not in atoms:atoms[a]=len(atoms)
  return atoms[a]
 def run(rows):
  env={n:intern(('input',n)) for n in parent['parameters']+parent['auxiliaries']}
  at=lambda n:intern(('constant',n)) if type(n)is int else env[n]
  for n,op,a,b in rows:env[n]=intern(('proved_coefficient',)) if n==L9 else intern((op,at(a),at(b)))
  return env
 a=run(parent['polynomial_source']);b=run(child['polynomial_source']);need(parent['comparisons']==child['comparisons'],'same comparisons')
 for n in set(a)&set(b):need(a[n]==b[n],'same surviving full-source register')
 for i,pair in enumerate(parent['comparisons']):need(a[f'sos_res{i}']==b[f'sos_res{i}'],'same complete residual')
 need(a[parent['output']]==b[child['output']],'same whole polynomial')
 return {'shared_register_identities':len(set(a)&set(b)),'residual_identities':len(parent['comparisons']),'complete_polynomial_identities':1}

def verify(root):
 root=Path(root);counts=Counter();forms=[];rng=random.Random(6311047303)
 for variant in VARIANTS:
  parent=canonical_parent(root,variant);child=rewrite(root,variant,parent)
  proof=_local_identity(parent,child);counts.update(_whole_identity(parent,child));counts['local_coefficient_identities']+=1
  pref=child['transfer']['prefix'];ports=child['parameters']+child['auxiliaries']
  for i in range(48):
   if i<16:
    values={n:rng.randrange(1,6) for n in ports}
    if child['domains']['parameters']=='natural':values.update({n:rng.randrange(0,5) for n in child['parameters']})
   else:values={n:rng.randrange(-4,5) for n in ports}
   if i>=32:values={n:Fraction(v,5) for n,v in values.items()};counts['rational_complete_cases']+=1
   a=_execute(parent['polynomial_source'],values);b=_execute(child['polynomial_source'],values)
   need(a[parent['output']]==b[child['output']],'whole numeric equality');counts['whole_numeric_cases']+=1
   for l,r in child['comparisons']:
    at=lambda e,v:v if type(v)is int else e[v]
    need(at(a,l)-at(a,r)==at(b,l)-at(b,r),'each complete comparison residual');counts['numeric_residual_identities']+=1
   if i<32:need(evaluate(root,child,values,signed=i>=16)==b[child['output']],'guarded public evaluator');counts['public_evaluations']+=1
  # k=eta+zeta is a retained equation, never usable in this identity proof.
  values={n:1 for n in ports};values[pref+'k']=3;env=_execute(child['source'],values)
  need(env[pref+'R10b']==2 and env[pref+'factored_first_base']*(env[pref+'factored_first_base']+env[pref+'R10b'])!=env[pref+'L9'],'computed-ratio off-zero counterfeit rejected')
  counts['wrong_k_counterexamples']+=1
  def reject(fn):
   try:fn()
   except ValueError:counts['bad_caller_rejections']+=1
   else:raise ValueError('malformed caller accepted')
  for key in child:
   bad=copy.deepcopy(child);del bad[key];reject(lambda bad=bad:checked(root,bad))
  for i,row in enumerate(child['polynomial_source']):
   bad=copy.deepcopy(child);bad['polynomial_source'][i][1]='+' if row[1]!='+' else '*';reject(lambda bad=bad:checked(root,bad))
  for packet,isparent in [(parent,True),(child,False)]:
   for key in ['source','comparisons','parameters','auxiliaries']:
    bad=copy.deepcopy(packet);bad[key]=tuple(bad[key]);reject(lambda bad=bad,isparent=isparent:rewrite(root,variant,bad) if isparent else checked(root,bad))
   bad=copy.deepcopy(packet);bad['certificate_ledger']['M']=float(bad['certificate_ledger']['M']);reject(lambda bad=bad,isparent=isparent:rewrite(root,variant,bad) if isparent else checked(root,bad))
  ones={n:1 for n in ports}
  for value in [True,1.0,Fraction(1),None]:
   vals=ones.copy();vals[ports[0]]=value;reject(lambda vals=vals:evaluate(root,child,vals,signed=True))
  for flag in [0,1,None,'true']:reject(lambda flag=flag:evaluate(root,child,ones,signed=flag))
  for vals in [dict(ones,extraneous=1),{n:v for n,v in ones.items() if n!=ports[0]}]:reject(lambda vals=vals:evaluate(root,child,vals))
  for name in child['auxiliaries'][:1]+child['parameters'][:1]:
   vals=ones.copy();vals[name]=-1;reject(lambda vals=vals:evaluate(root,child,vals))
  # Natural raw parameters include zero; standalone AND ports remain positive.
  vals=ones.copy();vals[child['parameters'][0]]=0
  if child['domains']['parameters']=='natural':evaluate(root,child,vals);counts['natural_zero_parameter_accepts']+=1
  else:reject(lambda:evaluate(root,child,vals))
  for getter in [lambda:canonical_parent(root,variant),lambda:build(root,variant),lambda:checked(root,child)]:
   a=getter();a['source'][0][0]='poison';a['parent_metadata']['poison']=1;need('poison' not in getter()['parent_metadata'] and getter()['source'][0][0]!='poison','defensive nested copies');counts['copy_checks']+=1
  old=parent['polynomial_ledger'];new=child['polynomial_ledger']
  forms.append(dict(variant=variant,parent_certificate_ledger=parent['certificate_ledger'],parent_polynomial_ledger=old,packet=child,local_coefficient_expansion=proof))
 for value in [True,1,1.0,None,'missing',('and_prescribed',)]:
  try:build(root,value)
  except ValueError:counts['bad_variant_rejections']+=1
  else:raise ValueError('bad variant')
 # Re-authentication is unconditional: corrupt every dependency after warm builds.
 with tempfile.TemporaryDirectory(prefix='native-first-coefficient-') as temp:
  path=Path(temp)
  for name in PINS:(path/name).write_bytes((root/name).read_bytes())
  for name in PINS:
   before=(path/name).read_bytes();(path/name).write_bytes(before+b'\n')
   variant='clock_incdec' if name.startswith('three_mass') else 'and_positive_scale' if name.startswith('native_binary_positive') else 'and_prescribed'
   try:build(path,variant)
   except ValueError:counts['warm_pin_rejections']+=1
   else:raise ValueError('changed authenticated dependency accepted')
   (path/name).write_bytes(before)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--root',str(root)],capture_output=True,text=True,timeout=30)
 need(proc.returncode!=0 and 'without -O' in proc.stderr,'optimized mode rejected');counts['optimized_mode_rejections']+=1
 return dict(status='PASS_NATIVE_PELL_FACTORED_FIRST_COEFFICIENT',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,forms=forms,counts=dict(counts),
 scope='Six authenticated complete sources, all-value same-coordinate polynomial identities. Prescribed AND63 and four current unbounded raw-input exact-clock circuits; no universality decoder, new variable bound, or saving in already-translated first norm units claimed.')

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact typed saved receipt')
 if v.output:v.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'polynomials':{f['variant']:f['packet']['polynomial_ledger']['operations'] for f in r['forms']}},sort_keys=True))
if __name__=='__main__':main()
