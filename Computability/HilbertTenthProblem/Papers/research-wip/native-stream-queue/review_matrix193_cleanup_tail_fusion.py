#!/usr/bin/env python3
"""Independent reconstruction and automatic one-Q-cut comparison; no old execution."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
AUTHOR={
 'matrix193_cleanup_tail_fusion.py':'52113307be60663b792a5ac62a7dc18ca35355d1a534faba4163c9b6d6047089',
 'matrix193_cleanup_tail_fusion.json':'61cbef79077bc3c5527c71f0abbeaac967f3d342f83bb8b9019ccdaa89857fe1',
 'matrix193_cleanup_tail_fusion.md':'0791bf4f25ae06e5ea4729de70da27d201524b57596756d991ad1af8253ebcc6'}
PARENT={
 'matrix193_selector_scaled_composition.py':'b220ba4a91370af19be84ab215dab3cf844dca16d026c08d7c0a8e85c62f6639',
 'matrix193_selector_scaled_composition.json':'762692a86d5020ffe89357d875803e927750546dbd946e309a2b48b6df73ce29',
 'matrix193_selector_scaled_composition.md':'96e6bc689c02ba789de5bed95b091a7560aba3a6a43a1428c6e0f3038bd61b5a',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
PLANS=[('cp302','cp272','cp297','cp283'),('cp304','cp274','cp300','cp284')]
CUBICS=[[7428465,45977311,-1503457720,-9305414129],[-63328274,-391960351,838975671,5192707423]]
DELETED=['cp'+str(i) for i in range(285,302)]+['cp303']
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def defs(rows):
 out={}
 for r in rows:
  ck(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  ck(type(n)is str and n not in out and o in ['+','-','*'],'SSA/opcode')
  ck(all(type(v) in [str,int] for v in [a,b]),'operand type');out[n]=r
 return out
def plus(a,b,s=1):
 d=dict(a)
 for k,c in b.items():d[k]=d.get(k,0)+s*c
 return {k:c for k,c in d.items() if c}
def times(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
 return {k:c for k,c in d.items() if c}
def op(o,a,b):return times(a,b) if o=='*' else plus(a,b,1 if o=='+' else -1)
def sparse(rows,root,cuts):
 d=defs(rows);z=(0,)*len(cuts);e={n:{tuple(int(i==j) for i in range(len(cuts))):1} for j,n in enumerate(cuts)}
 def visit(n):
  if type(n)is int:return {z:n} if n else {}
  if n not in e:
   ck(n in d,'unbound symbolic cone');_,o,a,b=d[n];e[n]=op(o,visit(a),visit(b))
  return e[n]
 return visit(root)
def record(p):return [[list(k),v] for k,v in sorted(p.items())]
def check_source(p):
 d=defs(p['source']);known=set(p['free']);ck(len(known)==len(p['free']),'unique free values')
 ck(known==set(p['witnesses'])|set(p['fixed_numerals'])|{'x'},'complete interface')
 degrees={n:int(n not in p['fixed_numerals']) for n in known};counts=Counter()
 for n,o,a,b in p['source']:
  ck(n not in known and all(type(v)is int or v in known for v in [a,b]),'topological source')
  x,y=[0 if type(v)is int else degrees[v] for v in [a,b]]
  degrees[n]=x+y if o=='*' else max(x,y);known.add(n);counts[o]+=1
 seen=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in d:todo.extend(d[n][2:])
 ck(seen==known,'all rows/ports live')
 return dict(total=len(d),M=counts['*'],A=counts['+']+counts['-'],witnesses=len(p['witnesses']),ports=len(p['free']),syntactic_degree_upper=degrees[p['output']],all_live=True)
def reconstruct(old,m):
 d={n:r[:] for n,r in defs(old['source']).items()};newrows=[]
 for j,(target,state,_,copy) in enumerate(PLANS):
  state=m(state)
  for k in [3,2,1,0]:
   nm=f'cleanup_tail_{j}_mul_{k}';na=f'cleanup_tail_{j}_add_{k}'
   ck(nm not in d and na not in d,'fresh names')
   d[nm]=[nm,'*',state,m('r108')];d[na]=[na,'+',nm,CUBICS[j][k]]
   newrows.extend([nm,na]);state=na
  d[m(target)]=[m(target),'+',state,m(copy)]
 for n in DELETED:del d[m(n)]
 return d,newrows
def full_identity(old,new,Q):
 # Normalize EVERY polynomial in the one actual computed Q, not merely the
 # author's two cuts; ordinary expressions keep their actual upstream ports.
 pool={}
 def intern(x):
  if x not in pool:pool[x]=len(pool)
  return pool[x]
 seed={n:intern(('port',n)) for n in old['free']};results=[];polys=[]
 for p in [old,new]:
  e=dict(seed);pure={};qvalue=None
  for n,o,a,b in p['source']:
   get=lambda v:intern(('integer',v)) if type(v)is int else e[v]
   if n==Q:
    e[n]=intern((o,get(a),get(b)));qvalue=e[n];pure[n]={(1,):1}
   elif all(type(v)is int or v in pure for v in [a,b]):
    aa={(0,):a} if type(a)is int else pure[a];bb={(0,):b} if type(b)is int else pure[b]
    pure[n]=op(o,aa,bb);e[n]=intern(('polynomial_in_actual_Q',qvalue,tuple(sorted(pure[n].items()))))
   else:e[n]=intern((o,get(a),get(b)))
  results.append(e);polys.append(pure)
 common=set(defs(old['source']))&set(defs(new['source']))
 ck(results[0][Q]==results[1][Q],'same actual computed Q')
 ck(all(results[0][n]==results[1][n] for n in common),'whole-DAG retained identities')
 ck(results[0][old['output']]==results[1][new['output']],'whole polynomial identity')
 return len(common),polys

def trace_final(p,N):
 d=defs(p['source']);ids=set();r=d[p['output']];ck(r[1]=='-' and r[3]==1,'final offset');ids.add(r[0])
 r=d[r[2]];ck(r[1]=='*' and r[2]==N,'native multiplier');ids.add(r[0]);r=d[r[3]]
 ck(r[1]=='+' and r[3]==1,'one plus SOS');ids.add(r[0]);leaves=[]
 def walk(n):
  r=d[n];ids.add(n)
  if r[1]=='*':
   ck(r[2]==r[3],'residual square');leaves.append(r[2]);ids.add(r[2]);return
  ck(r[1]=='+','SOS sum');walk(r[2]);walk(r[3])
 walk(r[2]);ck(leaves==p['retained_residual_wires'],'all ordered residuals')
 ck(len(ids)==3*len(leaves)+2,'full finalizer size')
 return {n:d[n] for n in ids}
def build(root,author):
 for n,h in AUTHOR.items():ck(sha((author/n).read_bytes())==h,'author pin '+n)
 for n,h in PARENT.items():ck(sha((root/n).read_bytes())==h,'parent pin '+n)
 a=read(author/'matrix193_cleanup_tail_fusion.json');p=read(root/'matrix193_selector_scaled_composition.json');maps=read(root/'matrix193_entry_controller_charts.json')
 ck(a['source_sha256']==AUTHOR['matrix193_cleanup_tail_fusion.py'],'author helper binding')
 ck(p['source_sha256']==PARENT['matrix193_selector_scaled_composition.py'],'parent helper binding')
 ck(a['pins']==PARENT,'exact dependency declaration');snapshot=enc(p)
 oldlist,newlist=p['packets'],a['packets'];ck(len(oldlist)==len(newlist)==4,'all four variants')
 base=oldlist[0];names=[r[0] for r in base['source']]
 native=names[names.index('selection__bs_even'):names.index('eight_units')+1]
 grouped=['r'+str(i) for i in range(110,134)]+[n for n in names if n.startswith('grouped_population_sum_')]+['r103']
 ck(len(native)==63 and len(grouped)==97,'inherited protected row inventory')
 reports=[]
 for j,(old,new) in enumerate(zip(oldlist,newlist)):
  chart={} if j==0 else maps['packets'][j-1]['map'];m=lambda n:chart.get(n,n) if type(n)is str else n
  before,after=check_source(old),check_source(new);ob,nb=defs(old['source']),defs(new['source'])
  for field in ['variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output','retained_residual_wires','coefficient_certificates','selector_words','selector_ledger']:
   ck(old[field]==new[field],'retained metadata '+field)
  ck(new['source_sha256']==sha(enc(new['source'])),'child complete array binding')
  ck(new['parent_reference']['source_sha256']==sha(enc(old['source'])),'actual parent array binding')
  # Check every component renaming through the separately authenticated chart map.
  for r in base['coefficient_component']:
   expected=[m(r[0]),r[1],m(r[2]),m(r[3])];ck(ob[expected[0]]==expected,'all552 component map definitions')
  rebuilt,added=reconstruct(old,m);ck(rebuilt==nb,'independent all-row reconstruction')
  ck(set(ob)-set(nb)=={m(n) for n in DELETED},'exact deleted names')
  for n in DELETED:
   users=[r[0] for r in old['source'] if m(n) in r[2:]]
   ck(all(u in {m(x) for x in DELETED+['cp302','cp304']} for u in users),'private removed row')
  local_proofs=[]
  for k,(target,state,tail,copy) in enumerate(PLANS):
   cuts=[m('r108'),m(state),m(copy)];expected={(4,1,0):1,(0,0,1):1}
   expected.update({(i,0,0):v for i,v in enumerate(CUBICS[k])})
   x=sparse(old['source'],m(target),cuts);y=sparse(new['source'],m(target),cuts)
   ck(x==y==expected,'independent three-cut formula')
   ck(sparse(old['source'],m(tail),[m('r108')])=={(i,):v for i,v in enumerate(CUBICS[k])},'cubic coefficients')
   local_proofs.append(dict(target=m(target),actual_cut_names=cuts,coefficients=record(x)))
  matched,polys=full_identity(old,new,m('r108'))
  words=[]
  for cert in old['coefficient_certificates']:
   expected={(i,):v for i,v in enumerate(cert['ascending_coefficients']) if v};n=cert['wire']
   ck(polys[0][n]==polys[1][n]==expected,'full coefficient word')
   words.append(dict(wire=n,coefficients=len(cert['ascending_coefficients']),digest=sha(enc(record(expected)))))
  component_ids={r[0] for r in old['coefficient_component']}|set(added)
  comp=[r for r in new['source'] if r[0] in component_ids];cc=Counter(r[1] for r in comp)
  ck(comp==new['coefficient_component'] and (len(comp),cc['*'],cc['+']+cc['-'])==(550,302,248),'complete550 coefficient cone')
  selector=[r for r in old['shared_selector_component']];ck(len(selector)==242 and all(nb[r[0]]==r for r in selector),'242 selector definitions')
  ck(new['shared_selector_component']==[r for r in new['source'] if r[0] in {x[0] for x in selector}],'complete selector array')
  ck(all(nb[m(n)]==ob[m(n)] for n in native+grouped),'native63/group97 literal')
  of,nf=trace_final(old,m('eight_units')),trace_final(new,m('eight_units'));ck(of==nf,'literal full finalizer')
  ck((after['total'],after['M'],after['A'])==(before['total']-2,before['M']-2,before['A']),'complete savings')
  ck(after['total']==[1415,1412,1412,1409][j] and after['witnesses']==[141,140,140,139][j],'four ledgers')
  ck(new['ledger']['exact_degree']==old['ledger']['exact_degree']==[35587,53345,53347,71105][j],'inherited exact degrees')
  ck(after['syntactic_degree_upper']==new['ledger']['syntactic_degree_upper']==[36547,54785,54785,73023][j],'fresh syntactic degree')
  reports.append(dict(variant=new['variant'],ledger=after,retained_values_identical=matched,local_identities=local_proofs,
   coefficient_words=words,all552_component_bindings_checked=True,coefficient_component_rows=550,selector_literal=242,
   native_literal=63,group_population_literal=97,finalizer_rows=len(nf),ordinary_residuals=len(new['retained_residual_wires']),
   exact_degree_inherited=new['ledger']['exact_degree'],source_sha256=sha(enc(new['source'])),whole_polynomial_equal=True))
 ck(enc(p)==snapshot,'parent bytes immutable after all checks')
 return dict(status='PASS_INDEPENDENT_CLEANUP_TAIL_FUSION',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PARENT,
  reports=reports,scope=dict(four_full_sources=True,automatic_all_pure_Q_normalization=True,all_ring_identities=True,
   positive_zero_maps='identity to immediate parent only',older_terminal_IDLE_maps='ordinary-input only',
   exact_degrees_inherited_not_rederived=True,predecessor_execution=False,new_native_fixture=False))
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=p.parse_args();r=build(a.root,a.author_root or a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact independent receipt')
 print(r['status'],'four arrays,5648 rows,16 full words,4 full polynomial identities')
if __name__=='__main__':main()
