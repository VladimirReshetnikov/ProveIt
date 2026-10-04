#!/usr/bin/env python3
"""Finite provenance/census certificates for the proper-pivot exclusion theorem.
All predecessor files are authenticated and read inertly, never imported/run.
"""
import argparse, hashlib, itertools, json
from collections import Counter
from pathlib import Path
PINS={
 'complete84_auxiliary_nine_gate_frontier.py':'e4197911e04fe9379fb0801ce01559ec371e3955d025486a3f84644aa17d48e2',
 'complete84_auxiliary_nine_gate_frontier.json':'049de5ef5f2d46802801b6f88450a852b672b218040e224c262a2ac1e79341e1',
 'complete84_auxiliary_nine_gate_frontier.md':'ae4925e8bf330fcd1a5d1c0f529e982f0c5df018690a7ef81e4ca27cc5ad4cd2',
 'complete84_auxiliary_mixed_cut.py':'a77f326d98550ed21643d5f1ea2aa25d9dca7d9a7fdca26c40e8bf1cdf80c13a',
 'complete84_auxiliary_mixed_cut.json':'1aa60da5b6b7278efdfd8535d10ec8f9af604b729b1f95c124eca714721dfc47',
 'complete84_auxiliary_mixed_cut.md':'b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2',
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade'}
def check(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(p):
 def pairs(xs):
  d={}
  for k,v in xs:check(k not in d,'duplicate JSON key');d[k]=v
  return d
 def invalid(s):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=invalid)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def add(a,b,sign=1):
 d=dict(a)
 for m,c in b.items():
  d[m]=d.get(m,0)+sign*c
  if not d[m]:del d[m]
 return d
def multiply(a,b):
 d={}
 for x,c in a.items():
  for y,h in b.items():
   m=tuple(u+v for u,v in zip(x,y));d[m]=d.get(m,0)+c*h
 return {m:c for m,c in d.items() if c}
def encode(p):return [[list(m),c] for m,c in sorted(p.items())]
def graph(p):
 seen=set(p['free']);check(len(seen)==len(p['free']),'free uniqueness');deps={};count=Counter()
 for n,o,a,b in p['source']:
  check(n not in seen and o in ['+','-','*'],'unique arithmetic output')
  check(all(type(v)is int or (type(v)is str and v in seen) for v in [a,b]),'acyclic source')
  seen.add(n);deps[n]=(a,b);count[o]+=1
 live=set();todo=[p['output']]
 while todo:
  x=todo.pop()
  if type(x)is str and x not in live:live.add(x);todo.extend(deps.get(x,()))
 check(live==seen,'full liveness')
 check(len(deps)==84 and count['*']==47 and count['+']+count['-']==37,'unchanged84 ledger')
 return {'total':84,'M':47,'A':37,'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),'all_live':True,'source_array_sha256':sha(canonical(p['source']))}

def build(root):
 for n,pin in PINS.items():check(sha((root/n).read_bytes())==pin,'pin '+n)
 frontier=parse(root/'complete84_auxiliary_nine_gate_frontier.json');mixed=parse(root/'complete84_auxiliary_mixed_cut.json');original=parse(root/'complete84_scaled_strong_output.json')['packet']
 check(frontier['source_sha256']==PINS['complete84_auxiliary_nine_gate_frontier.py'],'frontier source binding')
 check(frontier['parent_packet']==original,'literal full parent provenance')
 check(frontier['attaining_packet']['source']==mixed['mixed_attaining_packet']['source'],'literal attaining provenance')
 check(frontier['theorems']['only_possible_at_most_nine_budget']=={'M':5,'A':4},'inherited budget premise')
 check(frontier['theorems']['monomial_producing_additions_in_that_budget']==1,'inherited unique cancellation premise')
 zero=(0,)*6;unit=[tuple(int(j==i) for j in range(6)) for i in range(6)]
 # Coordinate order Delta,c,i,f,T,R; all paid dependencies remain explicit.
 paid={zero,*unit,(0,2,0,0,0,0),(1,2,0,0,0,0)};q=(2,4,2,0,0,0)
 divisors=list(itertools.product(range(3),range(5),[1,2]));candidates=[]
 for a,b,e in divisors:
  U=(a,b,e,0,0,0);ways=[]
  if U==q:ways.append({'form':'alias','other':None})
  # This mirrors the mathematical one-i-product necessary condition, not
  # an exhaustive circuit search. All i-free multipliers are relaxed.
  if e==2:
   h=(2-a,4-b,0,0,0,0)
   if h!=zero:ways.append({'form':'times_i_free','other':list(h)})
  if tuple(2*t for t in U)==q:ways.append({'form':'square','other':list(U)})
  if tuple(x+y for x,y in zip(U,unit[2]))==q:ways.append({'form':'times_i','other':list(unit[2])})
  if not ways:continue
  check(U not in paid and U[2]>0,'nontrivial specialized pivot relation premise')
  proper=U!=q
  if proper:
   check(all(w['form']!='alias' and tuple(x+y for x,y in zip(U,w['other']))==q and any(w['other']) for w in ways),'strict later nonconstant Q multiplication')
  candidates.append({'U_exponents':list(U),'restoration_forms':ways,'outside_original_paid_linear_span':True,'vanishes_at_i_zero':True,'proper_divisor':proper,'status':'excluded' if proper else 'not_excluded','product_deletions_certified_by_companion':2 if proper else 1,'five_minus_deletions':3 if proper else 4,'inherited_V_W_product_lower_bound':4})
 inherited={tuple(item['U_exponents']) for item in frontier['necessary_cancellation_pivots']}
 check({tuple(item['U_exponents']) for item in candidates}==inherited and len(candidates)==17,'exact inherited seventeen pivot census')
 excluded=[p for p in candidates if p['proper_divisor']];remaining=[p for p in candidates if not p['proper_divisor']]
 check(len(excluded)==16 and len(remaining)==1 and tuple(remaining[0]['U_exponents'])==q,'sixteen proper pivots excluded')
 check(all(p['five_minus_deletions']<p['inherited_V_W_product_lower_bound'] for p in excluded),'strict product contradiction')
 # Independent local polynomial authentication of both saved complete84 arrays.
 variables={name:{unit[i]:1} for i,name in enumerate(['A','R10a','i','f','auxiliary_quotient','r_lhs'])}
 variables['c2']={(0,2,0,0,0,0):1};variables['Ac2']={(1,2,0,0,0,0):1}
 V={(0,1,0,1,1,0):1,(0,1,0,0,0,0):-1,(0,0,0,2,0,1):-1};W={(1,0,0,2,0,0):1};Q={q:1};S=add(W,Q,-1)
 expected={'aux_u_rhs':V,'scaled_f_square':W,'R16':Q,'norm_strong':S}
 private_old={'auxiliary_Tf','auxiliary_Tf_minus_one','auxiliary_c_Tf','auxiliary_R_f2'}
 replacement=[['mixed_cT','*','R10a','auxiliary_quotient'],['mixed_Rf','*','r_lhs','f'],['mixed_linear','-','mixed_cT','mixed_Rf'],['mixed_f_linear','*','f','mixed_linear'],['aux_u_rhs','-','mixed_f_linear','R10a']]
 oldnames=['auxiliary_Tf','auxiliary_Tf_minus_one','auxiliary_c_Tf','auxiliary_R_f2','aux_u_rhs']
 change=dict(zip(oldnames,replacement));rebuilt=[change.get(row[0],row) for row in original['source']]
 attaining=frontier['attaining_packet'];check(rebuilt==attaining['source'],'exact five-row attaining splice')
 common={r[0]:r for r in original['source'] if r[0] not in change}
 for row in attaining['source']:
  if row[0] in common:check(row==common[row[0]],'literal outside cone');check(not any(v in private_old for v in row[2:]),'no hidden old intermediate consumer')
 cuts=set(mixed['cut_rows']);newcuts=(cuts-set(oldnames))|{r[0] for r in replacement}
 for packet,cutset in [(original,cuts),(attaining,newcuts)]:
  env=dict(variables)
  for n,o,a,b in packet['source']:
   if n not in cutset:continue
   aa=env[a] if type(a)is str else ({zero:a} if a else {});bb=env[b] if type(b)is str else ({zero:b} if b else {})
   env[n]=multiply(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
  for name,poly in expected.items():check(env[name]==poly,'exact local polynomial '+name)
  local_counts=Counter(row[1] for row in packet['source'] if row[0] in cutset)
  check(local_counts['*']==7 and local_counts['+']+local_counts['-']==3,'attaining local7M3A ledger')
  graph(packet)
 # Only V,Q,S cross the local boundary; W remains inside that boundary.
 external={n:[] for n in cuts}
 for n,o,a,b in original['source']:
  if n not in cuts:
   for v in [a,b]:
    if v in cuts:external[v].append(n)
 check({n for n,v in external.items() if v}=={'aux_u_rhs','R16','norm_strong'},'full local consumer boundary')
 check(original['free']==attaining['free'] and original['witnesses']==attaining['witnesses'] and len(original['witnesses'])==18,'unchanged paid coordinate domain')
 return {'schema':'complete84-auxiliary-proper-pivot-exclusion-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'variable_order':['Delta','c','i','f','T','R'],'paid_monomial_exponents':[list(e) for e in sorted(paid)],'pivot_census':candidates,'excluded_proper_pivots':16,'unexcluded_pivots':[list(q)],'parent_packet':original,'attaining_packet':attaining,'parent_ledger':graph(original),'attaining_ledger':graph(attaining),'local_ledger':{'M':7,'A':3,'total':10},'local_polynomials':{n:encode(p) for n,p in expected.items()},'external_cut_consumers':external,'theorem':{'at_most_nine_budget':{'M':5,'A':4},'only_possible_cancellation_pivot_up_to_nonzero_scalar':'Q=Delta^2*i^2*c^4','arbitrary_interleaving_allowed':True,'arbitrary_nonhomogeneous_products_allowed':True,'new_V_W_five_product_lower_bound':False,'all_nine_gate_circuits_excluded':False,'new_improved_complete_source':False},'proof_boundary':'The symbolic deletion argument is the companion theorem, not a bounded circuit search or a machine formalization. The finite receipt authenticates its monomial premises,17-to-1 census, and unchanged complete84 source interface. No compiler-only identities or extra paid ports are assumed.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:check(exact(r,parse(a.expect)),'type-exact receipt mismatch')
 print('PASS:16 proper pivots excluded;only cancellation output U=Q remains;unchanged84=47M37A/18w source verified')
if __name__=='__main__':main()
