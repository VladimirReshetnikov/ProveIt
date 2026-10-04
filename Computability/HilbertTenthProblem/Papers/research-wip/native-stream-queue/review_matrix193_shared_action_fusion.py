"""Independent full-array and exact sparse-polynomial review of action fusion.
No predecessor or author Python module is imported or executed.
"""
import argparse,json,hashlib
from pathlib import Path
from collections import Counter
SUBJECT={
'matrix193_shared_action_fusion.py':'e54e4d04c394ed5c889c6ff48d59c6dd2bfd1cd6af56513d0be949bf16725ed8',
'matrix193_shared_action_fusion.json':'6dcdd1dfe0b4dbc71c9263c45dc5773d39672673db3ef3742c6ecc63222eb1ca',
'matrix193_shared_action_fusion.md':'7f0cecc15a52cf7f2262dbe3cee1c751f7bbe545ff8fc2fa97029359d1084488'}
PARENTS={
'matrix193_joint_state_factor.py':'a146ffe90c441c288a71acef624e58ec5b35f8f210747fdcc76fcb7210df6df7',
'matrix193_joint_state_factor.json':'dfcd4ae7ab908804b141a0fe4feb93be8b31c3cc776a3ad2fbe78136ce71e154',
'matrix193_joint_state_factor.md':'d0032f9c9ba8975983c7fabf5399e6b1b590751598a61e53879d0a80f95fffce',
'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
def require(ok,msg):
 if not ok:raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def encode(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def obj(xs):
  d={}
  for k,v in xs:require(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(x):raise ValueError('not integer JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_float=bad,parse_constant=bad)
def defs(rows):
 d={}
 for row in rows:
  require(type(row)is list and len(row)==4,'row shape');n,o,a,b=row
  require(type(n)is str and n not in d and o in('+','-','*'),'SSA/op')
  require(type(a)in(int,str)and type(b)in(int,str),'operand type');d[n]=(o,a,b)
 return d
def audit(p):
 rows=p['source'];d=defs(rows);seen=set(p['free']);deg={n:0 if n in p['fixed_numerals']else 1 for n in seen}
 for n,o,a,b in rows:
  require(n not in seen and all(type(x)is int or x in seen for x in(a,b)),'all sequential operands')
  da,db=[0 if type(x)is int else deg[x]for x in(a,b)];deg[n]=da+db if o=='*'else max(da,db);seen.add(n)
 needed=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in needed:continue
  needed.add(n)
  if n in d:todo.extend(d[n][1:])
 require(needed==set(d)|set(p['free']),'all rows and supplied ports live')
 ops=Counter(r[1]for r in rows)
 return dict(total=len(rows),M=ops['*'],A=ops['+']+ops['-'],syntactic_degree=deg[p['output']],live_ports=len(p['free']))
def postorder(d,ports,root):
 # Iterative depth-first reconstruction, separate from author's recursion.
 done=set(ports);active=set();todo=[(root,False)];rows=[]
 while todo:
  n,exit=todo.pop()
  if type(n)is int or n in done:continue
  require(n in d,'defined dependency')
  if exit:
   require(all(type(v)is int or v in done for v in d[n][1:]),'dependencies reconstructed')
   active.remove(n);done.add(n);rows.append([n,*d[n]])
  else:
   require(n not in active,'cycle');active.add(n);todo.append((n,True))
   for v in reversed(d[n][1:]):
    if type(v)is str and v not in done:todo.append((v,False))
 require(set(d)<=done,'all expected definitions reached')
 return rows

def plus(a,b,sign=1):
 d=dict(a)
 for m,c in b.items():d[m]=d.get(m,0)+sign*c
 return {m:c for m,c in d.items()if c}
def times(a,b):
 d={}
 for i,x in a.items():
  for j,y in b.items():d[i+j]=d.get(i+j,0)+x*y
 return {m:c for m,c in d.items()if c}
def pure_source(rows,Q,ports,intern):
 ids={n:intern(('supplied',n))for n in ports};polys={};qbinding=None
 for n,o,a,b in rows:
  ai=intern(('integer',a))if type(a)is int else ids[a]
  bi=intern(('integer',b))if type(b)is int else ids[b]
  expr=intern(('binary',o,ai,bi))
  if n==Q:
   qbinding=expr;polys[n]={1:1};ids[n]=expr
  elif all(type(v)is int or v in polys for v in(a,b)):
   require(qbinding is not None,'actual computed Q precedes normalization')
   pa=({0:a}if a else{})if type(a)is int else polys[a]
   pb=({0:b}if b else{})if type(b)is int else polys[b]
   pp=times(pa,pb)if o=='*'else plus(pa,pb,1 if o=='+'else-1)
   polys[n]=pp;ids[n]=intern(('exact_sparse_ZQ',qbinding,tuple(sorted(pp.items()))))
  else:ids[n]=expr
 return ids,polys,qbinding

def local_expand(d,root,cuts):
 dim=len(cuts);memo={n:{tuple(int(i==j)for i in range(dim)):1}for j,n in enumerate(cuts)}
 zero=(0,)*dim
 def visit(n):
  if type(n)is int:return {zero:n}if n else{}
  if n in memo:return memo[n]
  o,a,b=d[n];aa,bb=visit(a),visit(b)
  if o=='*':
   result={}
   for x,c in aa.items():
    for y,v in bb.items():
     key=tuple(i+j for i,j in zip(x,y));result[key]=result.get(key,0)+c*v
  else:result=plus(aa,bb,1 if o=='+'else-1)
  memo[n]={k:v for k,v in result.items()if v};return memo[n]
 return visit(root)
def final_rows(d,output,unit):
 chosen={}
 def take(n):chosen[n]=d[n];return d[n]
 o,a,b=take(output);require(o=='-'and b==1,'output minus1')
 o,a,b=take(a);require(o=='*'and a==unit,'actual eight-unit binding')
 o,a,b=take(b);require(o=='+'and b==1,'one plus SOS')
 stack=[a];res=[]
 while stack:
  n=stack.pop();o,a,b=take(n)
  if o=='+':stack.append(b);stack.append(a)
  else:require(o=='*'and a==b,'square');take(a);res.append(a)
 return chosen,res

def build(root,author):
 for base,pins in[(root,PARENTS),(author,SUBJECT)]:
  for name,pin in pins.items():require(digest((base/name).read_bytes())==pin,'byte pin '+name)
 par=read(root/'matrix193_joint_state_factor.json');obj=read(author/'matrix193_shared_action_fusion.json');maps=read(root/'matrix193_entry_controller_charts.json')
 snapshots=(encode(par),encode(obj),encode(maps))
 require(obj['source_sha256']==SUBJECT['matrix193_shared_action_fusion.py'],'author helper binding')
 require(par['source_sha256']==PARENTS['matrix193_joint_state_factor.py'],'parent helper binding')
 require(len(par['packets'])==len(obj['packets'])==4,'four complete arrays')
 results=[];totalwords=totalentries=totalrows=0
 for j,(old,new)in enumerate(zip(par['packets'],obj['packets'])):
  mp={}if j==0 else maps['packets'][j-1]['map']
  def m(n):
   if type(n)is int:return n
   if n.startswith('joint_factor_'):return 'joint_factor_'+mp.get(n[13:],n[13:])
   return mp.get(n,n)
  od,nd=defs(old['source']),defs(new['source'])
  for pp in(old,new):require(digest(encode(pp['source']))==pp['source_sha256'],'full array binding')
  # Independently check every mapped 540-row parent coefficient definition.
  baseline=defs(par['packets'][0]['coefficient_component']);oc=defs(old['coefficient_component'])
  require({m(n):(o,m(a),m(b))for n,(o,a,b)in baseline.items()}==oc,'all540 original coefficient mappings')
  removed={m('cp'+str(i))for i in list(range(484,492))+list(range(494,502))+[503,506]}
  targets=[m('cp504'),m('cp507')];expected=dict(od)
  for n in removed:require(n in expected,'old private row');del expected[n]
  introduced={}
  # Reconstruct s=p*u+q*v, then z+s*A using the fixed action columns.
  inputs=[(m('cp480'),m('cp415')),(m('cp483'),m('cp493'))]
  for k,(u,v)in enumerate(inputs):
   introduced['fusion_u'+str(k)]=('*',m('r138'),u)
   introduced['fusion_v'+str(k)]=('*',m('cp129'),v)
   introduced['fusion_s'+str(k)]=('+','fusion_u'+str(k),'fusion_v'+str(k))
  for k,(a,b)in enumerate([(-489,-895),(271,496)]):
   introduced['fusion_a'+str(k)]=('*',a,'fusion_s0');introduced['fusion_b'+str(k)]=('*',b,'fusion_s1')
   introduced['fusion_out'+str(k)]=('+','fusion_a'+str(k),'fusion_b'+str(k))
   expected[targets[k]]=('+',m('cp502'if k==0 else'cp505'),'fusion_out'+str(k))
  require(not set(introduced)&set(od),'fresh registers');expected.update(introduced)
  require(expected==nd,'every new definition reconstructed')
  require(postorder(expected,new['free'],new['output'])==new['source'],'entire literal array order reconstructed')
  require(set(od)-set(nd)==removed and set(nd)-set(od)==set(introduced),'exact removed/added identifiers')
  require({n for n in od if n in nd and od[n]!=nd[n]}==set(targets),'exact two retained edits')
  users={n:sorted(row[0]for row in old['source']if n in row[2:])for n in removed}
  require(all(set(v)<=removed|set(targets)for v in users.values()),'complete private consumer closure')
  nc=defs(new['coefficient_component']);require(len(nc)==534 and set(nc)==set(oc)-removed|set(introduced),'whole534 component')
  require(all(nd[n]==od[n]for n in set(od)-set(oc)),'every non-coefficient row literal')
  for key in['free','fixed_numerals','witnesses','fixture_fixed_bindings','retained_residual_wires','selector_words','shared_selector_component','coefficient_certificates']:
   require(old[key]==new[key],'unchanged interface/data '+key)
  require(len(new['shared_selector_component'])==242,'selector242')
  for row in new['shared_selector_component']:require(nd[row[0]]==tuple(row[1:]),'literal selector producer')
  old_literals={x for row in old['source']for x in row[2:]if type(x)is int};new_literals={x for row in new['source']for x in row[2:]if type(x)is int}
  require(old_literals==new_literals and len(new_literals)==143,'unchanged143 fixed literals')
  a,b=audit(old),audit(new)
  require(b['total']==[1399,1396,1396,1393][j]and(a['total']-b['total'],a['M']-b['M'],a['A']-b['A'])==(6,4,2),'full paid reduction')
  require(all(new['ledger'][k]==b[k]for k in ['total','M','A']),'reported complete count')
  cc=Counter(row[1]for row in new['coefficient_component']);require((len(nc),cc['*'],cc['+']+cc['-'])==(534,288,246),'coefficient cost')
  require(new['ledger']['positive_witnesses']==[141,140,140,139][j]and len(new['free'])==[150,149,149,148][j],'all supplied coordinates')
  # Exact eight-port verification at the ACTUAL old/new source boundary.
  cuts=[m(n)for n in ['cp480','cp483','cp415','cp493','r138','cp129','cp502','cp505']]
  local=[]
  for k,n in enumerate(targets):
   lhs,rhs=local_expand(od,n,cuts),local_expand(nd,n,cuts);require(lhs==rhs,'independent eight-port identity')
   expected_poly={}
   for coord,coef in enumerate([(-489,-895),(271,496)][k]):
    for variable,power in[(coord,4),(coord+2,5)]:
     ex=[0]*8;ex[variable]=ex[power]=1;expected_poly[tuple(ex)]=coef
   ex=[0]*8;ex[6+k]=1;expected_poly[tuple(ex)]=1
   require(lhs==expected_poly,'exact matrix-action coefficients')
   local.append({'wire':n,'terms':[[list(e),v]for e,v in sorted(lhs.items())]})
  # Sparse polynomial normalization differs from the author's dense engine.
  pool={}
  def intern(key):
   if key not in pool:pool[key]=len(pool)
   return pool[key]
  Q=m('r108');iv0,pv0,q0=pure_source(old['source'],Q,old['free'],intern);iv1,pv1,q1=pure_source(new['source'],Q,new['free'],intern)
  require(q0==q1,'actual computed Q has identical full ancestry expression')
  require(pv0[m('r138')]==pv1[m('r138')]=={18:1}and pv0[m('cp129')]==pv1[m('cp129')]=={60:1},'both paid Q powers')
  common=set(od)&set(nd);require(all(iv0[n]==iv1[n]for n in common),'all retained actual values identical')
  require(iv0[old['output']]==iv1[new['output']],'whole polynomial identity at actual inputs')
  words=[]
  for cert in old['coefficient_certificates']:
   n=cert['wire'];want={i:c for i,c in enumerate(cert['ascending_coefficients'])if c}
   require(pv0[n]==pv1[n]==want,'entire coefficient word')
   words.append({'wire':n,'entries':len(cert['ascending_coefficients']),'nonzero_terms':len(want),'exact_sparse_coefficients':[[i,c]for i,c in sorted(want.items())]})
   totalwords+=1;totalentries+=len(cert['ascending_coefficients'])
  f0,r0=final_rows(od,old['output'],m('eight_units'));f1,r1=final_rows(nd,new['output'],m('eight_units'))
  require(f0==f1 and r0==r1==old['retained_residual_wires'],'all actual finalizer rows and ordered residuals')
  require(len(f1)==[50,47,47,44][j]and len(r1)==[16,15,15,14][j],'complete interleaved finalizer sizes')
  require(new['ledger']['exact_degree']==old['ledger']['exact_degree']==[35587,53345,53347,71105][j],'same-polynomial exact degree transfer')
  require(a['syntactic_degree']==b['syntactic_degree']==[36547,54785,54785,73023][j],'independent syntactic degree')
  require(len(common)==[1387,1384,1384,1381][j],'common register count')
  totalrows+=len(new['source'])
  results.append({'variant':new['variant'],'ledger':b,'coefficient_rows':len(nc),'full_array_reconstructed':True,'all_retained_values_equal':len(common),
   'exact_local_cut':local,'pure_Q_values_old':len(pv0),'pure_Q_values_new':len(pv1),'all_coefficient_words':words,
   'actual_Q_wire':Q,'exact_expression_nodes':len(pool),'finalizer_rows':len(f1),'residuals':r1,
   'private_consumer_map':users,'inherited_exact_degree':new['ledger']['exact_degree']})
 require((totalrows,totalwords,totalentries)==(5584,16,2704),'complete scope totals')
 require((encode(par),encode(obj),encode(maps))==snapshots,'all parsed sources unchanged')
 return dict(status='PASS_INDEPENDENT_SHARED_ACTION_FUSION',source_sha256=digest(Path(__file__).read_bytes()),subject=SUBJECT,parents=PARENTS,
  complete_rows=totalrows,coefficient_words=totalwords,coefficient_entries=totalentries,packets=results,
  scope='Exact complete-source reconstruction and sparse actual-Q-bound identities. Exact degrees inherited by polynomial equality; no new native histories, full leading-form proof, or global arithmetic lower bound.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root,a.author_root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:require(encode(read(a.expect))==encode(result),'type-exact independent receipt')
 print(result['status'],result['complete_rows'],result['coefficient_words'],result['coefficient_entries'])
if __name__=='__main__':main()
