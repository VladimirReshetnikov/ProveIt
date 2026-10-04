"""Independent inert-array audit of the four selector/scaled-power compositions."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

AUTHOR_PINS={
 'matrix193_selector_scaled_composition.py':'b220ba4a91370af19be84ab215dab3cf844dca16d026c08d7c0a8e85c62f6639',
 'matrix193_selector_scaled_composition.json':'762692a86d5020ffe89357d875803e927750546dbd946e309a2b48b6df73ce29',
 'matrix193_selector_scaled_composition.md':'96e6bc689c02ba789de5bed95b091a7560aba3a6a43a1428c6e0f3038bd61b5a',
}
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
def ck(v,s):
 if not v:raise ValueError(s)
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):
 def pairs(v):
  d={}
  for k,x in v:ck(k not in d,'duplicate key');d[k]=x
  return d
 def bad(v):raise ValueError('noninteger JSON '+v)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(p):return {r[0]:r for r in p['source']}
def closure(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in d:todo.extend(d[n][2:])
 return seen

def check_array(p):
 seen=set(p['free']);ck(len(seen)==len(p['free']),'free duplicates')
 ck(seen==set(p['witnesses'])|set(p['fixed_numerals'])|{'x'},'interface')
 deg={n:0 if n in p['fixed_numerals']else 1 for n in seen};c=Counter()
 for r in p['source']:
  ck(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  ck(type(n)is str and n not in seen and o in ('+','-','*'),'SSA/operation')
  ck(all(type(v)is int or type(v)is str and v in seen for v in (a,b)),'topology/types')
  da,db=(0 if type(v)is int else deg[v] for v in (a,b))
  deg[n]=da+db if o=='*'else max(da,db);seen.add(n);c[o]+=1
 ck(closure(table(p),[p['output']])==seen,'complete liveness')
 return {'rows':len(p['source']),'M':c['*'],'A':c['+']+c['-'],'witnesses':len(p['witnesses']),
         'fixed_ports':len(p['fixed_numerals']),'all_ports':len(p['free']),
         'distinct_literals':len({v for r in p['source']for v in r[2:]if type(v)is int}),
         'syntactic_degree_upper':deg[p['output']]}

def add(a,b,sgn=1):
 d=a.copy()
 for i,c in b.items():d[i]=d.get(i,0)+sgn*c
 return {i:c for i,c in d.items() if c}
def mul(a,b):
 d={}
 for i,c in a.items():
  for j,e in b.items():d[i+j]=d.get(i+j,0)+c*e
 return {i:c for i,c in d.items() if c}
def univariate(p,Q):
 e={Q:{1:1}}
 for n,o,a,b in p['source']:
  if n==Q or any(type(v)is str and v not in e for v in (a,b)):continue
  av=e[a]if type(a)is str else {0:a};bv=e[b]if type(b)is str else {0:b}
  e[n]=mul(av,bv)if o=='*'else add(av,bv,1 if o=='+'else-1)
 return e

def congruence(old,new,Q,po,pn):
 # Normalize every pure-Q subexpression independently. Its Q token is the
 # actual whole input-bearing expression, not an extra free coordinate.
 pool={}
 def intern(t):
  if t not in pool:pool[t]=len(pool)
  return pool[t]
 ports={n:intern(('port',n))for n in old['free']}
 def interpret(p,polys):
  e=ports.copy()
  for n,o,a,b in p['source']:
   if n in polys and n!=Q:
    coeff=tuple(sorted(polys[n].items()))
    if any(i>0 for i,c in coeff):ck(Q in e,'paid actual Q');e[n]=intern(('poly',e[Q],coeff))
    else:e[n]=intern(('constant',polys[n].get(0,0)))
   else:
    av,bv=(intern(('constant',v))if type(v)is int else e[v]for v in(a,b))
    e[n]=intern((o,av,bv))
  return e
 a=interpret(old,po);b=interpret(new,pn)
 ck(a[Q]==b[Q],'actual Q expression equality')
 ck(all(a[n]==v for n,v in b.items()),'every retained whole register equality')
 return len(new['source'])

def tail(p):
 d=table(p);r=d[p['output']];ck(r[1]=='-'and r[3]==1,'output minus one')
 product=d[r[2]];ck(product[1]=='*','native final product')
 n=product[2];one=d[product[3]];ck(one[1]=='+'and one[3]==1,'one plus SOS')
 names={r[0],product[0],one[0]};res=[]
 def expand(k):
  r=d[k];names.add(k)
  if r[1]=='+':expand(r[2]);expand(r[3])
  else:
   ck(r[1]=='*'and r[2]==r[3]and r[2]in d,'exact square leaf')
   names.add(r[2]);res.append(r[2])
 expand(one[2]);ck(res==p['retained_residual_wires']and len(set(res))==len(res),'all residuals exactly once')
 ck(len(names)==3*len(res)+2,'full tail count')
 ck(all(not any(v in names for v in row[2:])for row in p['source']if row[0]not in names),'private finalizer')
 return n,[r for r in p['source']if r[0]in names]

def build(root,author):
 for n,h in AUTHOR_PINS.items():ck(sha((author/n).read_bytes())==h,'author pin '+n)
 result=read(author/'matrix193_selector_scaled_composition.json')
 ck(result['source_sha256']==AUTHOR_PINS['matrix193_selector_scaled_composition.py'],'author source binding')
 pins=result['pins'];ck(len(pins)==9,'nine dependencies')
 for n,h in pins.items():ck(sha((root/n).read_bytes())==h,'dependency '+n)
 old=read(root/'matrix193_selector_block_sharing.json')['packets']
 scaled=read(root/'matrix193_scaled_power_reuse.json')['packets']
 maps=read(root/'matrix193_entry_controller_charts.json')['packets']
 ck(len(old)==len(scaled)==len(result['packets'])==4,'four complete arrays')
 records=[]
 for i,(p,q,s)in enumerate(zip(old,result['packets'],scaled)):
  m={}if i==0 else maps[i-1]['map'];w=lambda n:m.get(n,n)
  for field in ['variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output','retained_residual_wires']:
   ck(p[field]==q[field],'unchanged interface '+field)
  a,b=table(p),table(q);dead=set(a)-set(b);added=set(b)-set(a)
  changed=[n for n in b if b[n]!=a.get(n)]
  ck(dead=={w('cp344')}and not added and changed==[w('cp345')],'independently derived definition delta')
  target=changed[0];deleted=next(iter(dead));Q=w('r108')
  ck(a[target]==[target,'*',-20,deleted],'old scalar multiply')
  ck(b[target]==[target,'*',w('cp317'),w('cp400')],'new product')
  ck([r[0]for r in p['source']if deleted in r[2:]]==[target],'deleted power private')
  ck(target not in closure(a,[Q])and deleted not in closure(a,[Q]),'Q independent of edit')
  po,pn=univariate(p,Q),univariate(q,Q)
  ck(po[target]==pn[target]=={162:-20},'target coefficient identity')
  ck(po[deleted]=={162:1}and po[w('cp317')]=={150:1}and po[w('cp400')]=={12:-20},'paid operand identities')
  ck(all(po[n]==v for n,v in pn.items()),'all retained pure-Q values')
  checked=congruence(p,q,Q,po,pn)
  ck([n for n in a if n not in po and n in b]==[n for n in b if n not in po],'non-Q order')
  ids={r[0]for r in p['coefficient_component']};comp=[r for r in q['source']if r[0]in ids]
  ck(comp==q['coefficient_component']==s['coefficient_component'],'literal552 scaled component')
  cc=Counter(r[1]for r in comp);ck((len(comp),cc['*'],cc['+']+cc['-'])==(552,304,248),'coefficient ledger')
  selids={r[0]for r in p['shared_selector_component']};sel=[r for r in q['source']if r[0]in selids]
  ck(sel==q['shared_selector_component']==p['shared_selector_component'],'literal242 selector component')
  ck(q['selector_words']==p['selector_words'],'selector word contracts')
  sc=Counter(r[1]for r in sel);ck((len(sel),sc['*'],sc['+']+sc['-'])==(242,121,121),'selector ledger')
  coefficient_entries=0
  ck(q['coefficient_certificates']==p['coefficient_certificates']==s['coefficient_certificates'],'coefficient interfaces')
  for c in q['coefficient_certificates']:
   coeff={j:v for j,v in enumerate(c['ascending_coefficients'])if v}
   ck(pn[c['wire']]==po[c['wire']]==coeff,'full coefficient polynomial')
   coefficient_entries+=len(c['ascending_coefficients'])
  native0,t0=tail(p);native1,t1=tail(q);ck(native0==native1 and t0==t1,'whole finalizer equality')
  native_names=[r[0]for r in old[0]['source']];n0=native_names.index('selection__bs_even');n1=native_names.index('eight_units')
  native=[w(n)for n in native_names[n0:n1+1]]
  groups=[w('r'+str(k))for k in range(110,134)]+[w(n)for n in native_names if n.startswith('grouped_population_sum_')]+[w('r103')]
  ck(len(native)==63 and len(groups)==97 and all(a[n]==b[n]for n in native+groups),'literal native/group boundary')
  led=check_array(q);prior=check_array(p)
  ck((led['rows'],led['M'],led['A'])==([1417,1414,1414,1411][i],[685,684,684,683][i],[732,730,730,728][i]),'literal complete count')
  ck(led['rows']==prior['rows']-1 and led['M']==prior['M']-1 and led['A']==prior['A'],'one paid M saving')
  ck(led['witnesses']==[141,140,140,139][i]and led['fixed_ports']==8 and led['distinct_literals']==137,'domain/literals')
  degree=[35587,53345,53347,71105][i]
  ck(q['ledger']['exact_degree']==p['ledger']['exact_degree']==p['degree_transfer']['exact_degree']==degree,'exact degree transfer')
  records.append(dict(variant=q['variant'],ledger=led,deleted=a[deleted],old_target=a[target],new_target=b[target],
    all_retained_registers_equal=checked,actual_Q_expression_bound=True,pure_Q_registers_checked=len(pn),
    coefficient_rows=len(comp),coefficient_entries=coefficient_entries,selector_rows=len(sel),native_rows=63,group_rows=97,
    finalizer_rows=len(t1),residuals=len(q['retained_residual_wires']),exact_degree_inherited=degree,
    source_sha256=sha(canonical(q['source'])),coefficient_component_sha256=sha(canonical(comp))))
 return dict(status='PASS_INDEPENDENT_SELECTOR_SCALED_COMPOSITION',source_sha256=sha(Path(__file__).read_bytes()),
  author_pins=AUTHOR_PINS,dependency_pins=pins,packets=records,
  complete_rows=sum(r['ledger']['rows']for r in records),coefficient_entries=sum(r['coefficient_entries']for r in records),
  scope='Entire polynomial identity on identical supplied variables to the selector-sharing parent; degree inherited through that identity; no predecessor execution, no new accepting trajectory, no stronger inverse for older terminal/IDLE charts')
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--author-root',type=Path,default=Path('/tmp'))
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=build(a.root,a.author_root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(r,indent=2,sort_keys=True)+'\n')
 else:ck(canonical(r)==canonical(read(a.expect)),'exact reviewer receipt')
 print(r['status'],r['complete_rows'],'rows;',r['coefficient_entries'],'coefficient entries')
if __name__=='__main__':main()
