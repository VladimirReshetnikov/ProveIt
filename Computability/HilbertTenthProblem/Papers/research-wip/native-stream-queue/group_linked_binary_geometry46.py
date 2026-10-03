#!/usr/bin/env python3
"""Exact coefficient refactoring of the two complete geometry47/49 sources.

Standard library only; authenticated source receipts, no historical imports.
The shared-B population interpretation keeps its external scale hypothesis.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
import hashlib,json,random,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'group_linked_binary_geometry47.py': 'f3368a4676138275a5329a4f53b63e918fb3dab7a7a9e143ec8edb0a8216b58f', 'group_linked_binary_geometry47.json': 'd1c7c541bed3d1c584460c826973a885b00c65a03990ced28e2d6997db8af3f9', 'group_linked_binary_geometry47.md': '4be87c7429b89e171417ce54065b575947cea21e9bb1986112cee0ad0a259f96', 'native_binary_three_row_fifo58.py': 'c245a16893f62001f10dc734b949539835d5c43e6deb6cb3ef322872ef826800', 'native_controller_binary_selector56.py': 'd21de8fc373c5a55a30efdcf5a3171c06f80568a9edfdb98d5176fc2767494b1', 'native_binary_input_dilation132.md': '4e0e04e1004f3371b95003f999af7a3bf5aea034788e42261e55ade96ee189fc', 'native_binary_input_dilation132.py': '4734230670ee87464fd6df4f884904a4351c51b257ae8d87d21d5c362d086df7', 'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f'}
BLOCK=['UM2','scaled_norm_coefficient','ratio_product2','L9']
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def encoded(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def execute(source,values):
 e=dict(values)
 for n,op,a,b in source:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e

def inspect(source,terminals,free):
 need(type(source)is list and type(free)is list and len(free)==len(set(free)),'Exact source and distinct supplied ports')
 ready=set(free);nodes={};counts=Counter()
 for row in source:
  need(type(row)is list and len(row)==4,'Exact four-field gate')
  n,op,a,b=row
  need(type(n)is str and n not in ready and type(op)is str and op in ['+','-','*'],'Fresh legal gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in (a,b)),'Typed closed operands')
  ready.add(n);nodes[n]=(a,b);counts[op]+=1
 live=set();pending=list(terminals)
 while pending:
  n=pending.pop()
  if type(n)is not str or n in live:continue
  need(n in ready,'Known comparison/output port');live.add(n)
  if n in nodes:pending.extend(nodes[n])
 need(live==set(nodes)|set(free),'Every gate and supplied coordinate live')
 return dict(operations=len(source),M=counts['*'],A=counts['+']+counts['-'],all_gates_live=True)

def finalizer(rows,pairs):
 out=deepcopy(rows);last=None
 for i,(a,b) in enumerate(pairs):
  r=f'geometry_residual_{i}';s=f'geometry_square_{i}';out.extend([[r,'-',a,b],[s,'*',r,r]])
  if last is None:last=s
  else:n=f'geometry_sum_{i}';out.append([n,'+',last,s]);last=n
 return out,last

def authenticate(root):
 root=Path(root)
 need(bool(PINS),'Pinned inventory required')
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'Pinned source/proof '+name)
 return root

def canonical_parent(root,shared_B=True):
 need(type(shared_B)is bool,'Exact Boolean source mode');root=authenticate(root)
 receipt=json.loads((root/'group_linked_binary_geometry47.json').read_text())
 record=receipt['source'][0 if shared_B else 1]
 need(record['shared_B'] is shared_B,'Actual selected source variant')
 rows=record['source'];pairs=record['comparisons'];parameters=record['parameters'];aux=record['auxiliaries']
 need(parameters==(['q','B','J'] if shared_B else ['q','J']) and len(aux)==19 and len(pairs)==13,'Parent interface')
 if not shared_B:need(exact(rows[:2],[['geometry_q2','*','q','q'],['B','*',8,'geometry_q2']]),'Literal paid standalone B')
 core=rows[:-4] if shared_B else rows[2:-4]
 reverse=lambda v:{'J':'r','q':'n2'}.get(v,v) if type(v)is str else v
 unaliased=[[n,op,reverse(a),reverse(b)] for n,op,a,b in core]
 need(sha(json.dumps(unaliased,separators=(',',':')).encode())==receipt['core_sha256'],'Actual authenticated binary43 core and only input aliases')
 need(exact(rows[-4:],[['geometry_even','*',2,'odd_half'],['geometry_odd','+','geometry_even',1],['geometry_X_bound','+','J','bound_beta'],['geometry_index_bound','+','B','index_beta']]),'Unchanged three paid geometry conditions')
 need({n for n,op,a,b in rows if 'B' in (a,b)}=={'geometry_index_bound'},'Sole B consumer for inherited scale transport')
 ledger=inspect(rows,[v for pair in pairs for v in pair],parameters+aux)
 need((ledger['operations'],ledger['M'],ledger['A'])==((47,26,21) if shared_B else (49,28,21)),'Actual complete parent ledger')
 poly,out=finalizer(rows,pairs)
 return dict(shared_B=shared_B,source=rows,comparisons=pairs,parameters=parameters,auxiliaries=aux,
   certificate_ledger=ledger,polynomial_source=poly,output=out,polynomial_ledger=inspect(poly,[out],parameters+aux),
   source_sha256=sha(encoded(rows)),comparison_count=13,positive_auxiliary_count=19,
   semantic_contract=('Positive q,B,J with external B>=8q²; exact population projection J>B,J odd,q=2^popcount(J). The scale inequality is not computed by this component.' if shared_B else 'Positive q,J; B=8q² is computed internally. Exact population projection J>B,J odd,q=2^popcount(J).'),
   excluded_obligations='P power-of-two typing and (B-1)J+1=P are separate paid components; no universal computation source is claimed.')

def build(root,shared_B=True,supplied=None):
 old=canonical_parent(root,shared_B)
 if supplied is not None:need(exact(supplied,old),'Only entire canonical selected geometry parent')
 d={n:[op,a,b] for n,op,a,b in old['source']}
 want={'wn2':['*','w','q'],'sn2':['*','s','q'],'UM':['*','wn2','sn2'],'ksn2':['*','k','sn2'],
       'UM2':['*','UM','UM'],'scaled_norm_coefficient':['+','UM2','wn2'],
       'ratio_product2':['*','ksn2','ksn2'],'L9':['*','scaled_norm_coefficient','ratio_product2'],
       'tauplus1':['+','tau',1],'R9':['*','tau','tauplus1']}
 need(all(exact(d.get(n),row) for n,row in want.items()),'Actual supplied-k coefficient and unchanged half-binomial root')
 for name,consumer in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
  need({n for n,op,a,b in old['source'] if name in(a,b)}=={consumer},'Only declared private consumers')
  need(all(name not in pair for pair in old['comparisons']),'Private producer is not an exported comparison operand')
 need('first_root_base' not in d and 'first_next' not in d,'Fresh local names')
 rows=[]
 for n,op,a,b in old['source']:
  if n=='L9':rows.extend([['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base','k'],['L9','*','first_root_base','first_next']])
  elif n not in BLOCK:rows.append([n,op,a,b])
 p=deepcopy(old);p['source']=rows;p['source_sha256']=sha(encoded(rows));free=p['parameters']+p['auxiliaries']
 p['certificate_ledger']=inspect(rows,[v for pair in p['comparisons'] for v in pair],free)
 p['polynomial_source'],p['output']=finalizer(rows,p['comparisons']);p['polynomial_ledger']=inspect(p['polynomial_source'],[p['output']],free)
 p['transformation']=dict(parent_source_sha256=old['source_sha256'],same_all_value_comparison_polynomials=True,
   same_all_value_SOS_polynomial=True,coordinate_map='identity',actual_k_port='k',unchanged_root='tau*(tau+1)',
   unchanged_comparison_indices=list(range(13)),new_registers=['first_root_base','first_next'],removed_private_registers=BLOCK[:-1])
 p['degree_certificate']=dict(exact_coefficient_degree=14,exact_residual_degrees=[14,3,1,5,4,2,4,6,10,2,1,2,1 if shared_B else 2],
   exact_SOS_degree=28,unique_top_residual_index=0,coefficient_leading_monomial={'k':2,'q':6,'s':4,'w':2},
   SOS_leading_monomial={'k':4,'q':12,'s':8,'w':4},leading_coefficient=1,
   method='Complete sparse polynomial expansion in all supplied coordinates; unique highest residual square.')
 need(p['certificate_ledger']==dict(operations=46 if shared_B else 48,M=25 if shared_B else 27,A=21,all_gates_live=True),'Complete new comparison ledger')
 need(p['polynomial_ledger']==dict(operations=84 if shared_B else 86,M=38 if shared_B else 40,A=46,all_gates_live=True),'Complete paid thirteen-square finalizer')
 return p

def checked(root,p):
 need(type(p)is dict and type(p.get('shared_B'))is bool,'Exact canonical packet/mode')
 expected=build(root,p['shared_B']);need(exact(p,expected),'Only complete typed canonical successor packet');return expected

def polynomial_source(root,p):
 p=checked(root,p);return p['polynomial_source'],p['output']
def evaluate(root,p,values,*,signed=False):
 p=checked(root,p);need(type(signed)is bool,'Exact Boolean arithmetic-domain flag')
 need(type(values)is dict and set(values)==set(p['parameters']+p['auxiliaries']),'Complete exact supplied assignment')
 need(all(type(x)is int for x in values.values()),'Exact integer coordinates')
 need(signed or all(x>0 for x in values.values()),'Strictly positive supplied coordinates')
 return execute(p['polynomial_source'],values)[p['output']]

def sparse(source,free):
 d=len(free);zero=(0,)*d
 def add(a,b,sign=1):
  c=dict(a)
  for m,v in b.items():c[m]=c.get(m,0)+sign*v
  return {m:v for m,v in c.items() if v}
 def times(a,b):
  c={}
  for m,v in a.items():
   for n,w in b.items():
    t=tuple(x+y for x,y in zip(m,n));c[t]=c.get(t,0)+v*w
  return {m:v for m,v in c.items() if v}
 env={n:{tuple(int(i==j) for j in range(d)):1} for i,n in enumerate(free)}
 for n,op,a,b in source:
  a=env[a] if type(a)is str else {zero:a};b=env[b] if type(b)is str else {zero:b}
  env[n]=times(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return env,add,times

def degree_certificate(root,p):
 p=checked(root,p);free=p['parameters']+p['auxiliaries'];env,sub,mul=sparse(p['polynomial_source'],free)
 get=lambda v:env[v] if type(v)is str else {(0,)*len(free):v}
 rs=[sub(get(a),get(b),-1) for a,b in p['comparisons']]
 degree=lambda f:max(sum(m) for m in f)
 degrees=[degree(f) for f in rs];meta=p['degree_certificate']
 need(degrees==meta['exact_residual_degrees'],'Complete exact symbolic residual degrees')
 F=env[p['output']];D=degree(F);leaders={m:c for m,c in F.items() if sum(m)==D}
 expected=tuple(meta['SOS_leading_monomial'].get(n,0) for n in free)
 need(D==28 and leaders=={expected:1},'Exact full SOS leading polynomial')
 coeff=env['L9'];lead=tuple(meta['coefficient_leading_monomial'].get(n,0) for n in free)
 need(degree(coeff)==14 and {m:c for m,c in coeff.items() if sum(m)==14}=={lead:1},'Actual coefficient leading polynomial')
 serial=lambda f:[[list(m),c] for m,c in sorted(f.items())]
 return dict(variable_order=free,exact_degree=D,expanded_SOS_terms=serial(F),residual_term_counts=[len(f) for f in rs],
   residual_degrees=degrees,full_SOS_sha256=sha(encoded(serial(F))),unique_top_coefficient=1)

def verify(root):
 root=authenticate(root);rng=random.Random(462026);counts=Counter();forms=[]
 for shared in [True,False]:
  old=canonical_parent(root,shared);p=build(root,shared);free=p['parameters']+p['auxiliaries']
  oe,sub,mul=sparse(old['polynomial_source'],free);ne,_,_=sparse(p['polynomial_source'],free)
  for i,(a,b) in enumerate(p['comparisons']):
   need(oe[a]==ne[a] and oe[b]==ne[b],'Every full comparison operand identical');counts['complete_operand_polynomial_identities']+=2
   need(sub(oe[a],oe[b],-1)==sub(ne[a],ne[b],-1),'Every full residual polynomial identical');counts['complete_residual_polynomial_identities']+=1
  need(oe[old['output']]==ne[p['output']],'Entire literal SOS polynomial identical');counts['complete_SOS_polynomial_identities']+=1
  deg=degree_certificate(root,p)
  for i in range(192):
   signed=i>=96;v={n:rng.randrange(-4,5) if signed else rng.randrange(1,6) for n in free}
   if i%12==0:v={n:Fraction(x,2) for n,x in v.items()}
   a=execute(old['polynomial_source'],v);b=execute(p['polynomial_source'],v)
   need(a[old['output']]==b[p['output']],'Complete numeric same-coordinate identity')
   for left,right in p['comparisons']:need(a[left]-a[right]==b[left]-b[right],'All actual residual values');counts['numeric_residual_identities']+=1
   for n in set(a)&set(b):need(a[n]==b[n],'All retained register values');counts['shared_register_identities']+=1
   counts['complete_numeric_identities']+=1;counts['signed_cases']+=signed;counts['rational_cases']+=i%12==0
  # Explicit wrong-port off-zero challenge; both source modes supply k independently.
  v={n:1 for n in free};env=execute(old['source'],v);wrong=env['UM']*env['ksn2']*(env['UM']*env['ksn2']+env['R10b'])
  need(env['L9']==2 and wrong==3 and env['k']==1 and env['R10b']==2,'Actual supplied k is not R10b off zero')
  oldres=env['L9']-env['R9'];need((wrong-env['R9'])**2-oldres**2==1,'Concrete full SOS corruption from wrong k')
  counts['wrong_k_full_positive_regressions']+=1
  # Shared and standalone sources agree exactly under B=8q², including every auxiliary.
  if shared:
   standalone=build(root,False)
   for i in range(64):
    v={n:rng.randrange(-3,4) for n in standalone['parameters']+standalone['auxiliaries']};sv=dict(v,B=8*v['q']**2)
    a=execute(p['polynomial_source'],sv);b=execute(standalone['polynomial_source'],v)
    need(a[p['output']]==b[standalone['output']],'Full shared/computed-B identity');counts['shared_standalone_graph_identities']+=1
   # Exact inherited B-transport on arbitrary tuples satisfying the scale assumption.
   for q in range(1,9):
    B0=8*q*q
    for extra in range(8):
     v={n:1 for n in free};v.update(q=q,B=B0+extra,J=B0+extra+3,index_beta=3)
     transport=dict(v,B=B0,index_beta=3+extra)
     a=execute(p['source'],v);b=execute(p['source'],transport)
     need(all(a[x]-a[y]==b[x]-b[y] for x,y in p['comparisons']),'All13 exact scale-transport residuals')
     need(transport['index_beta']>0 and transport['B']>=8*q*q,'Scale transport retains positive domain');counts['shared_B_transport_identities']+=1
  def numeric_paths(x,path=()):
   if type(x)is dict:
    for k,v in x.items():yield from numeric_paths(v,path+(k,))
   elif type(x)is list:
    for i,v in enumerate(x):yield from numeric_paths(v,path+(i,))
   elif type(x)is int:yield path,x
  for original,parentmode in [(old,True),(p,False)]:
   bads=[]
   for path,v in list(numeric_paths(original)):
    for value in [float(v),bool(v),v+1]:
     bad=deepcopy(original);node=bad
     for k in path[:-1]:node=node[k]
     node[path[-1]]=value;bads.append(bad)
   bad=deepcopy(original);bad['source']=tuple(bad['source']);bads.append(bad)
   bad=deepcopy(original);bad['shared_B']=int(shared);bads.append(bad)
   bad=deepcopy(original);bad['parameters'].append('unpaid');bads.append(bad)
   for bad in bads:
    try:build(root,shared,bad) if parentmode else checked(root,bad)
    except (ValueError,TypeError,KeyError):counts['malformed_packet_rejections']+=1
    else:raise AssertionError('Noncanonical numeric/container packet accepted')
  for bad in [p,dict(old,source=p['source']),dict(old,shared_B=not shared)]:
   try:build(root,shared,bad)
   except ValueError:counts['no_op_or_wrong_parent_rejections']+=1
   else:raise AssertionError('Wrong parent accepted')
  v={n:1 for n in free};need(evaluate(root,p,v)==execute(p['polynomial_source'],v)[p['output']],'Exact public evaluator')
  for badval in [True,1.0,0,-1]:
   bad=dict(v,q=badval)
   try:evaluate(root,p,bad)
   except ValueError:counts['coordinate_type_domain_rejections']+=1
   else:raise AssertionError('Malformed positive coordinate accepted')
  for flag in [0,1,None,'yes']:
   for call in [lambda:build(root,flag),lambda:evaluate(root,p,v,signed=flag)]:
    try:call()
    except ValueError:counts['mode_type_rejections']+=1
    else:raise AssertionError('NonBoolean flag accepted')
  x=build(root,shared);x['source'][0][1]='-';need(build(root,shared)['source'][0][1]=='*','Isolated child copy');counts['copy_isolation_checks']+=1
  x=canonical_parent(root,shared);x['comparisons'][0]=['q','q'];need(canonical_parent(root,shared)['comparisons'][0]==['L9','R9'],'Isolated parent copy');counts['copy_isolation_checks']+=1
  forms.append(dict(shared_B=shared,parent_certificate=old['certificate_ledger'],parent_SOS=old['polynomial_ledger'],packet=p,exact_degree_expansion=deg))
 with tempfile.TemporaryDirectory(prefix='geometry46-pins-') as td:
  r=Path(td)
  for n in PINS:(r/n).write_bytes((root/n).read_bytes())
  build(r)
  for n in ['group_linked_binary_geometry47.json','native_binary_input_dilation132.md']:
   data=(r/n).read_bytes();(r/n).write_bytes(data+b' ')
   try:build(r)
   except ValueError:counts['rechecked_pin_rejections']+=1
   else:raise AssertionError('Changed pinned dependency accepted')
   (r/n).write_bytes(data)
 return dict(status='PASS_GEOMETRY46_COEFFICIENT_TRANSFER',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,forms=forms,counts=dict(counts),
  scope='All-value same-coordinate equality of every complete comparison and SOS polynomial. Shared46 assumes externally B>=8q² for its inherited population theorem; standalone48 computes B=8q². Both19 positive auxiliaries/13 comparisons. No P power typing, repunit equation, controller or universal source included. Exact SOS degree28, not just an upper bound.')

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();result=verify(v.root);raw=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if v.output:v.output.write_text(raw)
 target=v.expect if v.expect else (None if v.output else Path(__file__).with_suffix('.json'))
 if target:need(exact(json.loads(raw),json.loads(target.read_text())),'Fresh exact saved receipt')
 print(json.dumps({'status':result['status'],'counts':result['counts'],'ledgers':[(f['packet']['certificate_ledger'],f['packet']['polynomial_ledger']) for f in result['forms']]},sort_keys=True))
if __name__=='__main__':main()
