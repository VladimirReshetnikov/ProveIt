#!/usr/bin/env python3
"""A bounded exact successor of the frozen ant occurrence component.
Read predecessor files as authenticated bytes/JSON; never import or run them.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
PINS = {
 'ant48_rotated_occurrence_sharing.py': '8d6b1547b9bb8255e45d53e808606f4899ad704c12ec77d8132f12a5a5e350a9',
 'ant48_rotated_occurrence_sharing.json': 'a48ada7ad9e168c5ad3154ad9cfffeacc9286d799ad4481079401b7574da96b7',
 'ant48_rotated_occurrence_sharing.md': '56b0941a51f404747a70d1514ce8663f93f785dc3358e43d310d0635d8eed80f',
 'periodic_ant_endpoint_reuse48.json': 'b2dd16ebbe9f89adc85a161a897d9c86009233ac90a1e8214bb5879cc4c7cb98',
}
KINDS = ('DUP','NAND','MOVE_LEFT','MOVE_RIGHT')
def need(test, message):
 if not test: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def duplicate_free(pairs):
 d = {}
 for k,v in pairs:
  need(k not in d, 'duplicate key');d[k]=v
 return d
def read(b): return json.loads(b, object_pairs_hook=duplicate_free)
def canon(x): return json.dumps(x, sort_keys=True, separators=(',',':')).encode()
def transform(parent):
 c=parent['component'];aliases={p:p for p in c['input_bindings']};cache={};rows=[];events=[]
 for n,op,a,b in c['source']:
  need(n not in aliases and op in ['+','*'],'parent row');a=aliases[a];b=aliases[b]
  if op=='+' and 'paid_zero' in (a,b):
   aliases[n]=b if a=='paid_zero' else a;events.append([n,'add_zero',aliases[n]]);continue
  if op=='*' and 'paid_zero' in (a,b):
   aliases[n]='paid_zero';events.append([n,'mul_zero','paid_zero']);continue
  a,b=sorted((a,b));key=(op,a,b)
  if key in cache:
   aliases[n]=cache[key];events.append([n,'common_expression',cache[key]]);continue
  name='c'+str(len(rows));rows.append([name,op,a,b]);aliases[n]=name;cache[key]=name
 outputs={n:aliases[v] for n,v in c['outputs'].items()};live=set(outputs.values())
 for n,op,a,b in reversed(rows):
  if n in live: live.update((a,b))
 need(all(r[0] in live for r in rows),'unexpected dead row')
 ports={n:v for n,v in c['input_bindings'].items() if n in live}
 need(set(c['input_bindings'])-set(ports)=={'paid_zero'},'unused binding')
 counts=collections.Counter(e[1] for e in events)
 need(counts=={'add_zero':32,'mul_zero':4,'common_expression':32},'rewrite totals')
 return {'source':rows,'outputs':outputs,'input_bindings':ports,'rewrite_events':events,'rewrite_counts':dict(counts),'all_rows_live':True,'removed_input_binding':'paid_zero (still retained and paid elsewhere in parent full source)'}

def plus(a,b):
 c=dict(a)
 for m,k in b.items(): c[m]=c.get(m,0)+k
 return {m:k for m,k in c.items() if k}
def times(a,b):
 c={}
 for (e,t),k in a.items():
  for (f,u),v in b.items():
   need(t is None or u is None,'coefficient product outside linear ring')
   key=(e+f,u if t is None else t);c[key]=c.get(key,0)+k*v
 return {m:k for m,k in c.items() if k}
def check_component(c):
 values={'Y':{(1,None):1}}
 for k in KINDS:
  for s in range(957):
   n='T_'+k+'_'+str(s);values[n]={(0,n):1}
 need(set(values)==set(c['input_bindings']),'exact ports')
 counts=collections.Counter()
 for i,(n,op,a,b) in enumerate(c['source']):
  need(n=='c'+str(i) and n not in values and a in values and b in values,'closure')
  need(op in ['+','*'],'opcode');counts[op]+=1
  values[n]=plus(values[a],values[b]) if op=='+' else times(values[a],values[b])
 need(counts=={'+':3888,'*':3930},'new ledger')
 cert=[]
 for k in KINDS:
  for phase in [0,288000]:
   for b in range(3):
    name=f'{k}:{b}:{phase}'
    want={((480-b-s-phase//600)%960,'T_'+k+'_'+str(s)):1 for s in range(957)}
    got=values[c['outputs'][name]];need(got==want,'exact polynomial '+name)
    cert.append({'output':name,'terms':len(got),'coefficient_sha256':sha(canon([[e,t,v] for (e,t),v in sorted(got.items())]))})
 # Boundary regressions supplement all-coefficient identities.
 for y in [0,1,-1,3]:
  modulus=1000003;v={'Y':y%modulus}
  for k_i,k in enumerate(KINDS):
   for s in range(957):v['T_'+k+'_'+str(s)]=(17*k_i+s*s-11)%modulus
  for n,op,a,b in c['source']:v[n]=(v[a]+v[b] if op=='+' else v[a]*v[b])%modulus
  for k in KINDS:
   for phase in [0,288000]:
    for b in range(3):
     expected=sum(v['T_'+k+'_'+str(s)]*pow(y,(480-b-s-phase//600)%960,modulus) for s in range(957))%modulus
     need(v[c['outputs'][f'{k}:{b}:{phase}']]==expected,'numeric output')
 return {'M':3930,'A':3888,'total':7818,'input_bindings':3829,'output_polynomials':24,'exact_coefficient_terms':22968,'certificates':cert,'numeric_output_checks':96}

def verify(root):
 data={}
 for n,h in PINS.items():
  b=(root/n).read_bytes();need(sha(b)==h,'pin '+n);data[n]=b
 p=read(data['ant48_rotated_occurrence_sharing.json']);ep=read(data['periodic_ant_endpoint_reuse48.json'])
 need(p['component_audit']['M']==3950 and p['component_audit']['A']==3936,'parent ledger')
 c=transform(p);audit=check_component(c);whole={}
 for arity in ['2','1']:
  prior=p['inherited_complete_source_ledgers'][arity];base=ep['models'][arity]
  need(prior['total']==prior['M']+prior['A'],'parent complete sum')
  need(base['full_grammar_count_inherited_plus_verified_delta']['total']==14658925+(10 if arity=='1' else 0),'endpoint inherited sum')
  a={'M':prior['M']-20,'A':prior['A']-48,'total':prior['total']-68}
  a['with_endpoint_reuse']={'M':a['M']-9,'A':a['A'],'total':a['total']-9}
  need(a['total']==a['M']+a['A'],'new sum')
  need(a['with_endpoint_reuse']['total']==14620711+(10 if arity=='1' else 0),'combined sum')
  a['positive_witnesses']=prior['positive_witnesses'];a['equations']=prior['equations'];a['exact_degree_inherited']=prior['exact_degree_inherited_by_polynomial_identity'];whole[arity]=a
 return {'status':'PASS_EXACT_CLEANED_COMPONENT','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'component':c,'audit':audit,'new_source_sha256':sha(canon(c)),'saved_from_shared_component':{'M':20,'A':48,'total':68},'saved_from_original_24_horners':{'M':19086,'A':19128,'total':38214},'new_full_rotated_stage':{'M':3954,'A':3910,'total':7864},'derived_complete_grammars':whole,'scope':'Complete7818-row component and exact24 output identities. Complete grammar totals inherit unchanged frozen parts. No fullstream emission/hash or archived code execution. Paid zero is a proved parent expression, not a newly imposed equation.','full_stream_generated':False,'new_witnesses':0,'new_equations':0,'new_literals':0}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);g=a.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=a.parse_args()
 r=verify(args.root);s=json.dumps(r,indent=2)+'\n'
 if args.expect:need(args.expect.read_text()==s,'exact receipt')
 else:
  with args.output.open('x') as f:f.write(s)
 print(json.dumps({'status':r['status'],'M':3930,'A':3888,'total':7818,'additional_saving':68,'full_stream_generated':False}))
if __name__=='__main__':main()
