#!/usr/bin/env python3
"""Independent one-row source reconstruction; no author/predecessor imports."""
import argparse,json,hashlib
from pathlib import Path
from collections import Counter
PINS={
 'matrix193_scaled_power_reuse.py':'2186513567e31204f78726d856686be2818205638563e9b1cfa052b382177942',
 'matrix193_scaled_power_reuse.json':'c81bb0ef774361b1b8b4f1b6084ec90329f9c0e22665d8968ced5517959de2b4',
 'matrix193_scaled_power_reuse.md':'39114f292022ef9bd6dbd5065eed34c5634b77e4050556faa69ae2f656d466b8',
 'matrix193_terminal_power_composition.py':'2dc0fb36f50da402cc479673bb2c23a4354f9a80e23fb6f17857168fc1ad9cd1',
 'matrix193_terminal_power_composition.json':'c6456750337b4f87f55918d03760b5759606b772e298d37c0c5df9c92b87b623',
 'matrix193_terminal_power_composition.md':'7ea837d4def42b7b97577c3e5f4c421f73a8256ac1858890bdbcc2ad0a6948a3',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
def ck(t,s):
 if not t:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(p):
 def pairs(items):
  out={}
  for k,v in items:ck(k not in out,'duplicate key');out[k]=v
  return out
 def bad(s):raise ValueError(s)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def polynomials(rows,Q):
 env={Q:{1:1}}
 for n,op,a,b in rows:
  if n==Q or not all(type(v)is int or v in env for v in (a,b)):continue
  aa=({0:a}if a else {})if type(a)is int else env[a];bb=({0:b}if b else {})if type(b)is int else env[b]
  cc={}
  if op=='*':
   for i,c in aa.items():
    for j,d in bb.items():cc[i+j]=cc.get(i+j,0)+c*d
  else:
   cc=dict(aa)
   for i,c in bb.items():cc[i]=cc.get(i,0)+(c if op=='+'else-c)
  env[n]={i:c for i,c in cc.items()if c}
 return env

def finalizer(p,N):
 by={r[0]:r for r in p['source']};out=by[p['output']];ck(out[1]=='-'and out[3]==1,'output')
 prod=by[out[2]];ck(prod[1:3]==['*',N],'native multiplier');one=by[prod[3]];ck(one[1]=='+'and one[3]==1,'SOS+1')
 names={out[0],prod[0],one[0]};leaves=[]
 def descend(n):
  r=by[n];names.add(n)
  if r[1]=='*':
   ck(r[2]==r[3],'square');leaves.append(r[2]);names.add(r[2])
  else:ck(r[1]=='+','sum');descend(r[2]);descend(r[3])
 descend(one[2]);ck(leaves==p['retained_residual_wires'],'residual inventory')
 ck(len(names)==3*len(leaves)+2,'finalizer count')
 ck(all(not any(v in names for v in r[2:])for r in p['source']if r[0]not in names),'private finalizer')
 return [r for r in p['source']if r[0]in names]

def build(root,author):
 for n,h in PINS.items():
  folder=author if n.startswith('matrix193_scaled_power_reuse.')else root
  ck(sha((folder/n).read_bytes())==h,'pin '+n)
 old=parse(root/'matrix193_terminal_power_composition.json');new=parse(author/'matrix193_scaled_power_reuse.json');maps=parse(root/'matrix193_entry_controller_charts.json')
 ck(new['source_sha256']==PINS['matrix193_scaled_power_reuse.py'],'source binding');results=[]
 for i,(p,q)in enumerate(zip(old['packets'],new['packets'])):
  mapping={}if i==0 else maps['packets'][i-1]['map'];w=lambda n:mapping.get(n,n)
  before={r[0]:r for r in p['source']};gone=w('cp344');target=w('cp345');moved=w('cp400')
  ck(before[gone]==[gone,'*',w('r138'),w('r200')],'literal private producer')
  ck(before[target]==[target,'*',-20,gone],'literal target')
  ck(before[moved]==[moved,'*',-2,w('cp333')],'literal paid scalar power')
  ck([r[0]for r in p['source']if gone in r[2:]]==[target],'private producer sole consumer')
  positions={r[0]:j for j,r in enumerate(p['source'])}
  advance=[w('cp333')]if positions[w('cp333')]>positions[target]else []
  advance.append(moved)
  expected=[]
  for r in p['source']:
   if r[0]==gone or r[0]in advance:continue
   if r[0]==target:expected.extend([before[n]for n in advance]+[[target,'*',w('cp317'),moved]])
   else:expected.append(r)
  ck(expected==q['source'],'independent complete literal source reconstruction')
  for k in ('variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output','retained_residual_wires'):
   ck(p[k]==q[k],'same interface '+k)
  a,b=polynomials(p['source'],w('r108')),polynomials(q['source'],w('r108'))
  for n,poly in [('cp317',{150:1}),('cp333',{12:10}),('cp344',{162:1}),('cp345',{162:-20}),('cp400',{12:-20})]:ck(a[w(n)]==poly,'exact paid power '+n)
  ck(b[target]=={162:-20}and all(a[n]==v for n,v in b.items()),'all retained Q polynomials')
  known=set(q['free']);ct=Counter()
  for n,op,x,y in q['source']:
   ck(n not in known and op in ('+','-','*'),'producer');ck(all(type(v)is int or v in known for v in (x,y)),'paid operands');known.add(n);ct[op]+=1
  live=set();todo=[q['output']];by={r[0]:r for r in q['source']}
  while todo:
   n=todo.pop()
   if type(n)is str and n not in live:
    live.add(n)
    if n in by:todo.extend(by[n][2:])
  ck(live==known,'full liveness');ck((len(q['source']),ct['*'],ct['+']+ct['-'])==(p['ledger']['total']-1,p['ledger']['M']-1,p['ledger']['A']),'full cost')
  compnames={r[0]for r in p['coefficient_component']};comp=[r for r in q['source']if r[0]in compnames]
  ck(comp==q['coefficient_component']and len(comp)==552,'complete component')
  for cert in p['coefficient_certificates']:
   wanted={j:c for j,c in enumerate(cert['ascending_coefficients'])if c};ck(b[cert['wire']]==wanted,'entire coefficient')
  f=finalizer(p,w('eight_units'));ck(f==finalizer(q,w('eight_units')),'full finalizer literal')
  ck(q['ledger']['exact_degree']==p['ledger']['exact_degree'],'inherited degree')
  results.append({'variant':q['variant'],'rows':len(q['source']),'M':ct['*'],'A':ct['+']+ct['-'],'coefficient_rows':552,'full_coefficient_words':4,'finalizer_rows':len(f),'private_deletion_and_earlier_paid_operand':True,'all_retained_Q_polynomials':len(b),'same_supplied_interface':True,'all_live':True,'exact_degree_inherited':q['ledger']['exact_degree']})
 ck(len(results)==4,'all variants')
 return {'schema':'independent-scaled-power-review-v1','checker_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'results':results,'total_rows':sum(r['rows']for r in results),'frozen_code_executed_or_imported':False}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();result=build(a.root,a.author_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(exact(result,parse(a.expect)),'exact receipt')
 print('PASS independent6024rows;16 full coefficient polynomials;all private edits,paid dependencies,liveness,finalizers')
if __name__=='__main__':main()
