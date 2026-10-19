#!/usr/bin/env python3
"""Independent finite audit of a disjoint-support trace grammar.

This checks the dictionary, source interfaces, scanner bounds, and all routing
projections. It does not substitute for a literal-machine/runtime/blank proof.
"""
from pathlib import Path
from functools import cache
import argparse,json,hashlib,heapq,sys

def normal(word,independent):
 # A second implementation using full dependence edges, not the C++
 # last-occurrence optimization, makes the audit structurally independent.
 n=len(word);out=[];degree=[0]*n;edges=[[] for _ in word]
 for j,c in enumerate(word):
  for i,d in enumerate(word[:j]):
   if (c,d) not in independent:edges[i].append(j);degree[j]+=1
 queue=[(c,i) for i,c in enumerate(word) if not degree[i]];heapq.heapify(queue)
 while queue:
  c,i=heapq.heappop(queue);out.append(c)
  for j in edges[i]:
   degree[j]-=1
   if not degree[j]:heapq.heappush(queue,(word[j],j))
 assert len(out)==len(word)
 return ''.join(out)

def audit(candidate,inputs,fine=None):
 meta=json.loads((inputs/'input-provenance.json').read_text());data=json.loads(candidate.read_text())
 fine=Path(fine or meta['fine_path']);sys.path.insert(0,str(fine/'runtime/code'))
 from audit_fine_grammar import make_vocabulary
 source,terminals,orig_names,orig_allowed,encode=make_vocabulary()
 # Reconstruct the actual closed fine blocks and their supports from the
 # pinned source. Neither a supplied token table nor a supplied pair list
 # is accepted as a proof that two instructions commute.
 @cache
 def bounds(i):
  r=source['ast_dag'][i]
  if r[0]=='L':
   op,*args=r[1];return (1,0) if op=='dec' else (args[0],0) if op=='brk' else (0,args[0]) if op=='cont' else (0,0)
  a,b=map(bounds,r[1:]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
 @cache
 def fineword(i):
  r=source['ast_dag'][i];return fineword(r[1])+fineword(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
 @cache
 def footprint(i):
  r=source['ast_dag'][i]
  if r[0]=='L':
   op,*args=r[1];return (1<<args[0] if op in ('inc','dec') else 0,op=='halt')
  a,b=map(footprint,r[1:]);return a[0]|b[0],a[1] or b[1]
 ids=sorted({i for name in terminals.values() for i in fineword(source['atoms'][name]['ast'])});alphabet='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
 assert len(ids)==30
 tokens={alphabet[j]:dict(ast=i,support_mask=footprint(i)[0],has_halt=footprint(i)[1]) for j,i in enumerate(ids)}
 assert tokens==meta['tokens'] and all(bounds(i)==(0,0) for i in ids)
 independent={(a,b) for a,x in tokens.items() for b,y in tokens.items() if a!=b and not x['has_halt'] and not y['has_halt'] and not x['support_mask']&y['support_mask']}
 @cache
 def norm(w):return normal(w,independent)
 names={q:norm(w) for q,w in orig_names.items()};override=meta.get('source_override')
 if override:
  assert override['state']==76 and override['original_word']==orig_names[76]
  names[76]=norm(override['new_word'])
 terms={norm(w):name for w,name in terminals.items()};allowed={norm(w):m for w,m in orig_allowed.items()}
 assert len(terms)==len(terminals)==44
 rules={w:(a,b) for w,a,b in data['rules']}
 assert len(rules)==len(data['rules'])==data['rules_count']
 for w,(a,b) in rules.items():
  assert w==norm(w)==norm(a+b) and a==norm(a) and b==norm(b),(w,a,b)
  assert w not in terms
  assert len(a)<len(w) and len(b)<len(w)
  for side,c in enumerate((a,b)):
   assert c in rules or c in terms,(w,c)
   if c in terms:assert allowed[c]&(1<<side),(w,side,c)
 def project(w,bits):
  for bit in bits:
   assert w in rules;w=rules[w][int(bit)]
  return w
 routes={(r['source'],r['read']):r['word'] for r in data['routes']};assert len(routes)==len(data['routes'])==11
 symbols=json.loads((fine/'runtime/inputs/semantic-symbols.json').read_text());inv={name:c for c,name in symbols.items()};checked=[]
 for c in source['left_entry_projection_constraints']:
  reason=c['reason'];key=(reason['source'],reason['read']);bits=c['prefix']
  if 'via' in reason:assert reason['via']==177;bits=str(reason['previous'])+bits
  target=norm(encode(''.join(inv[t] for t in c['word'])))
  assert project(routes[key],bits)==target
  checked.append(dict(caller=key,prefix=bits,target=target))
 assert len(checked)==22
 released={24,89,107,152,154,175,188,207,213,245}
 for q in source['required_entry_roots']:
  if q not in released:assert names[q] in rules
 locks=(inputs/'locks.txt').read_text().splitlines();assert int(locks[0])==len(locks)-1==54
 for w,b,t in map(str.split,locks[1:]):assert project(norm(w),b)==norm(t)
 # The AST-height calculation expands actual chosen production trees.
 lines=(fine/'runtime/inputs/semantic.txt').read_text().splitlines();nr,nroot,na=map(int,lines[0].split());old={}
 for k,w,q in map(str.split,lines[1:nr+1]):old[norm(encode(w))]=(norm(encode(w[:int(k)])),norm(encode(w[int(k):])))
 byast={int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()};visiting=set()
 def join(a,b):return (1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2]))
 @cache
 def astprop(i):
  key=('A',i);assert key not in visiting;visiting.add(key)
  row=source['ast_dag'][i]
  value=wordprop(byast[i]) if i in byast else (0,0,0) if row[0]=='L' else join(astprop(row[1]),astprop(row[2]))
  visiting.remove(key);return value
 @cache
 def wordprop(w):
  key=('W',w);assert key not in visiting;visiting.add(key)
  value=astprop(source['atoms'][terms[w]]['ast']) if w in terms else join(*(wordprop(c) for c in (rules[w] if w in rules else old[w])))
  visiting.remove(key);return value
 props=astprop(source['original_ast']);assert list(props)==data['properties'] and props[1]<=6 and props[2]<=64
 # Independently realize the trace nodes as literal fine words. This is not
 # a TM compiler: it detects any discrepancy between the claimed trace and
 # the actual inherited terminal implementation at each abstract boundary.
 @cache
 def realize(w):
  if w in terms:
   name=terms[w];matches=[q for q,n in terminals.items() if n==name];assert len(matches)==1;return matches[0]
  return ''.join(realize(c) for c in rules[w])
 changes=[]
 for q,w in names.items():
  if w in rules:
   actual=realize(w);assert norm(actual)==w
   original=override['new_word'] if override and q==76 else orig_names[q]
   if actual!=original:changes.append(dict(source_state=q,tokens=len(actual),original_word=original,realized_word=actual))
 report=dict(status='PASS_FINITE_TRACE_IDEAL_AUDIT',grammar_roles=len(rules),retained_framework_roles=117,prospective_total_roles=117+len(rules),trace_pairs=len(independent)//2,route_cases=22,bootstrap_equations=54,properties=list(props),changed_source_interfaces=len(changes),realized_source_changes=changes,candidate_sha256=hashlib.sha256(candidate.read_bytes()).hexdigest(),source_override=override,scope='Finite exact grammar and trace identities only; no new binary machine, blank-start result, or complete runtime theorem.')
 return report

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,required=True);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--fine',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=audit(a.candidate,a.inputs,a.fine);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ('realized_source_changes','source_override')},indent=2))
