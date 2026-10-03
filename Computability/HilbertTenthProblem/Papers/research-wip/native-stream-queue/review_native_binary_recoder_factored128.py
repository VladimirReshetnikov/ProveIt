#!/usr/bin/env python3
"""Bounded independent two-cone delta audit from authenticated full receipts."""
import argparse,copy,hashlib,json,random
from pathlib import Path
from collections import Counter
from fractions import Fraction
PINS={'native_binary_recoder_factored128.py':'89537df180f20e46b0da8ecd0d4d2abb9a35d353b85acd03b57f981a3d1d1b08',
'native_binary_recoder_factored128.json':'83755b1bbc2688103770dda215eeeca8a38a3422956c31cd7cbd08e0d6118555',
'native_binary_recoder_factored128.md':'d02968062a48476f78f86a20531e6b4cf07f0de0aef3fa68361548d61cc1ee6c'}
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def ledger(rows,ports,ends):
 free=set(ports);known=set(free);nodes={};degree={n:1 for n in free};counts=Counter()
 need(len(free)==len(ports),'all declared coordinates distinct')
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row shape');n,op,a,b=row
  need(type(n)is str and n not in known and op in ('+','-','*'),'fresh opcode')
  need(all(type(x)is int or type(x)is str and x in known for x in (a,b)),'closed typed operands')
  ds=[degree[x] if type(x)is str else 0 for x in (a,b)];degree[n]=sum(ds) if op=='*' else max(ds)
  known.add(n);nodes[n]=(a,b);counts['M' if op=='*' else 'A']+=1
 live=set();used=set();todo=list(ends)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n in free:used.add(n);continue
  if n in live:continue
  need(n in nodes,'valid final port');live.add(n);todo.extend(nodes[n])
 need(live==set(nodes) and used==free,'complete liveness and entire coordinate interface')
 return dict(operations=len(rows),M=counts['M'],A=counts['A'],degree_upper=max(degree[n] if type(n)is str else 0 for n in ends))
def poly_local(rows,prefix):
 z=(0,0,0);e={prefix+'wn2':{(1,0,0):1},prefix+'sn2':{(0,1,0):1},prefix+'k':{(0,0,1):1}}
 def add(a,b,sign=1):
  out=a.copy()
  for m,v in b.items():out[m]=out.get(m,0)+sign*v
  return {m:v for m,v in out.items() if v}
 def mul(a,b):
  out={}
  for m,v in a.items():
   for n,w in b.items():
    q=tuple(x+y for x,y in zip(m,n));out[q]=out.get(q,0)+v*w
  return {m:v for m,v in out.items() if v}
 for n,op,a,b in rows:
  if n in e:continue
  if (type(a)is int or a in e) and (type(b)is int or b in e):
   a={z:a} if type(a)is int else e[a];b={z:b} if type(b)is int else e[b];e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return e[prefix+'L9']
def scalar(rows,v):
 e=dict(v)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e
def verify(root,subject_root):
 root=Path(root);subject_root=Path(subject_root)
 for name,pin in PINS.items():need(sha((subject_root/name).read_bytes())==pin,'subject pin '+name)
 rec=json.loads((subject_root/'native_binary_recoder_factored128.json').read_text())
 for name,pin in rec['pins'].items():need(sha((root/name).read_bytes())==pin,'actual source/receipt pin '+name)
 p=subject_root/'native_binary_recoder_factored128.py';api={'__name__':'_independent_recoder_delta','__file__':str(p)};exec(compile(p.read_bytes(),str(p),'exec'),api)
 native=json.loads((root/'native_binary_input_dilation130.json').read_text())['certificate'];grill=json.loads((root/'grill_tag_exact_width_loader.json').read_text())['complete']
 counts=Counter();forms=[]
 for form in rec['forms']:
  variant=form['variant'];child=form['packet'];old=api['canonical_parent'](root,variant)
  need(exact(api['build'](root,variant),child),'actual frozen child canonical packet')
  if variant=='exact_width_grill':
   need(old['source']==grill['source'] and old['polynomial_source']==grill['polynomial_source'] and old['comparisons']==grill['comparisons'],'entire actual exact-width parent sources')
   need(old['parameters']==grill['parameters'] and old['auxiliaries']==grill['auxiliaries'],'entire actual exact-width interface')
   widths=grill['loader']['constants']['width'];need(widths==784,'actual fixed block width')
  else:
   need(old['comparisons']==native['comparisons'] and old['parameters']==native['parameters'] and old['auxiliaries']==native['auxiliaries'],'complete native recoder interface')
   if variant=='inline4':need(old['source']==native['source'],'literal original inline130')
   else:
    width=old['width'];mu=width.bit_length()+width.bit_count()-2;need(old['source'][mu+1:]==native['source'][3:],'only original private power chain changed')
    powers={'q':1}
    for dest,op,a,b in old['source'][:mu]:need(op=='*' and a in powers and b in powers,'literal exponent chain');powers[dest]=powers[a]+powers[b]
    need(powers['Q']==width and old['source'][mu]==['B','*',1<<(width-1),'Q'],'paid exact fixed-width scale')
  ports=old['parameters']+old['auxiliaries'];ends=[x for pair in old['comparisons'] for x in pair]
  need(old['parameters']==child['parameters'] and old['auxiliaries']==child['auxiliaries'] and old['comparisons']==child['comparisons'],'complete coordinate/comparison conservation')
  need(old['domains']==child['domains'] and old['degree']==child['degree'] and old['parent_semantics']==child['parent_semantics'],'all unchanged domain/degree/scope metadata')
  d={n:[op,a,b] for n,op,a,b in old['source']};removed=set();replacement={};cuts=set()
  for prefix in child['prefixes']:
   n=lambda x:prefix+x
   need(d[n('UM')]==['*',n('wn2'),n('sn2')] and d[n('ksn2')]==['*',n('k'),n('sn2')] and n('k') in ports,'actual supplied k and computed products')
   for name,want in {'UM2':['*',n('UM'),n('UM')],'scaled_norm_coefficient':['+',n('UM2'),n('wn2')],'ratio_product2':['*',n('ksn2'),n('ksn2')],'L9':['*',n('scaled_norm_coefficient'),n('ratio_product2')]}.items():need(d[n(name)]==want,'literal old four-gate cone')
   for private,user in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
    key=n(private);need([r[0] for r in old['source'] if key in r[2:]]==[n(user)],'unique private consumer')
    need(all(key not in pair for pair in old['comparisons']) and all(key not in row[2:] for row in old['polynomial_source'][len(old['source']):]),'no comparison/finalizer private use');removed.add(key);counts['private_consumer_checks']+=1
   replacement[n('L9')]=[[n('factored_first_base'),'*',n('UM'),n('ksn2')],[n('factored_first_next'),'+',n('factored_first_base'),n('k')],[n('L9'),'*',n('factored_first_base'),n('factored_first_next')]];cuts.add(n('L9'))
   need(poly_local(old['source'],prefix)==poly_local(child['source'],prefix)=={(2,4,2):1,(1,2,2):1},'independent full local coefficient expansion');counts['coefficient_identities']+=1
  expected=[]
  for row in old['source']:
   if row[0] in replacement:expected.extend(replacement[row[0]])
   elif row[0] not in removed:expected.append(row)
  need(expected==child['source'],'only the two literal cones changed')
  tail=old['polynomial_source'][len(old['source']):];need(child['polynomial_source']==expected+tail and old['output']==child['output'],'entire finalizer literally retained')
  ids={}
  def intern(v):
   if v not in ids:ids[v]=len(ids)
   return ids[v]
  def graph(rows):
   e={n:intern(('port',n)) for n in ports};at=lambda x:intern(('integer',x)) if type(x)is int else e[x]
   for n,op,a,b in rows:e[n]=intern(('proved_local_coefficient',n)) if n in cuts else intern((op,at(a),at(b)))
   return e,at
  a,aa=graph(old['polynomial_source']);b,bb=graph(child['polynomial_source'])
  for name in set(a)&set(b):need(a[name]==b[name],'all surviving downstream registers');counts['shared_DAG_identities']+=1
  for left,right in old['comparisons']:need(aa(left)==bb(left) and aa(right)==bb(right),'complete residual identity');counts['residual_identities']+=1
  need(a[old['output']]==b[child['output']],'whole final polynomial identity');counts['full_polynomial_identities']+=1
  for q in [old,child]:
   need(ledger(q['source'],ports,ends)==q['certificate'] and ledger(q['polynomial_source'],ports,[q['output']])==q['polynomial'],'all complete ledgers/degrees/liveness');counts['complete_ledgers']+=2
  need(child['polynomial']['M']==old['polynomial']['M']-2 and child['polynomial']['A']==old['polynomial']['A'],'exactly two M saved')
  if variant=='exact_width_grill':
   need(all(n not in d for n in ['hist__and__UM2','hist__and__scaled_norm_coefficient','hist__and__ratio_product2','hist__and__L9']),'no third coefficient cone')
   need('hist__and__first_unit' in d and old['parent_semantics']['unit_register']==child['parent_semantics']['unit_register'],'history first unit and complete anchor unchanged')
  # Only bounded delta examples; the long history stays at J=0, not a claimed accepting zero.
  for case in range(3):
   v={n:(1 if case==0 else (i%5)-2) for i,n in enumerate(ports)}
   if case==2:v={n:Fraction(x,3) for n,x in v.items()}
   if variant=='exact_width_grill':v.update({n:1 for n in ports if n.startswith('hist__Shat')})
   ea=scalar(old['polynomial_source'],v);eb=scalar(child['polynomial_source'],v);need(ea[old['output']]==eb[child['output']],'bounded full numeric delta');counts['whole_numeric_cases']+=1
  if variant=='exact_width_grill':
   bad=copy.deepcopy(child);bad['polynomial_source'][-1][1]='+' if bad['polynomial_source'][-1][1]!='+' else '-'
  else:
   bad=copy.deepcopy(child);next(r for r in bad['source'] if r[0].endswith('factored_first_next'))[3]=child['prefixes'][0]+'R10b'
  try:api['checked'](root,bad)
  except ValueError:counts['actual_changed_packet_rejections']+=1
  else:raise ValueError('invalid packet accepted')
  forms.append({'variant':variant,'width':child['width'],'parent_polynomial':old['polynomial'],'child_certificate':child['certificate'],'child_polynomial':child['polynomial'],'positive_witnesses':len(child['auxiliaries']),'comparisons':len(child['comparisons']),'degree':child['degree']})
 return {'status':'PASS_INDEPENDENT_TWO_CONE_RECODER_TRANSFER','review_source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'dependencies':rec['pins'],'counts':dict(counts),'forms':forms,
 'scope':'Two literal supplied-k coefficient cones, entire actual recoder and exact-width source/finalizer preservation; no historical builder execution, accepting Pell tuple, new universal table, or third history saving.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--subject-root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.subject_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']},sort_keys=True))
if __name__=='__main__':main()
