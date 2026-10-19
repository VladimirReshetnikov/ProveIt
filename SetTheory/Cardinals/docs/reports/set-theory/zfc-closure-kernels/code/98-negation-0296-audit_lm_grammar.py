#!/usr/bin/env python3
"""Finite checker for the coupled LM source/route backend; no TM proof claim."""
from pathlib import Path
from functools import cache
import argparse,json,sys,hashlib

def audit(candidate,backend,fine=None):
 meta=json.loads(backend.read_text());fine=Path(fine or meta['fine_path']);sys.path.insert(0,str(fine/'runtime/code'))
 from audit_fine_grammar import make_vocabulary
 old,oldterms,oldnames,oldallowed,encode=make_vocabulary();assert old==meta['original_source']
 source=json.loads(json.dumps(old));assert source['ast_dag'][112]==['N',57,42] and source['ast_dag'][113]==['N',112,78]
 source['ast_dag'][112]=['N',40,42];source['ast_dag'][113]=['N',112,77];source['rules']['237']=[218,124];assert source==meta['source'];ast=source['ast_dag']
 @cache
 def bounds(i):
  r=ast[i]
  if r[0]=='L':
   op,*args=r[1];return (1,0) if op=='dec' else (args[0],0) if op=='brk' else (0,args[0]) if op=='cont' else (0,0)
  a,b=map(bounds,r[1:]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
 @cache
 def fineword(i):
  r=ast[i];return fineword(r[1])+fineword(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
 toks=sorted({t for name in oldterms.values() for t in fineword(source['atoms'][name]['ast'])});alphabet='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';enc={i:alphabet[j] for j,i in enumerate(toks)};assert len(toks)==30
 word=lambda i:''.join(enc[t] for t in fineword(i));names={int(q):word(int(i)) for q,i in source['sequence_ast_roots'].items()};terms={word(source['atoms'][name]['ast']):name for name in oldterms.values()};allowed={word(source['atoms'][name]['ast']):oldallowed[w] for w,name in oldterms.items()}
 override=meta.get('source_override')
 if override:
  inherited=override['inherited_fine_override']
  def contract(w):
   result=w.replace('LNPQMVQPW','LMPW')
   assert 'LNPQM' not in result,'AX prefix contraction requires its own interface theorem'
   return result
  assert override['state']==inherited['state']==76
  assert inherited['original_word']==oldnames[76] and override['original_word']==names[76]
  assert override['new_word']==contract(inherited['new_word'])
  names[76]=override['new_word']
 assert {str(q):w for q,w in names.items()}==meta['names'] and terms==meta['terminals'] and allowed==meta['allowed']
 assert len(terms)==44 and len(set(names.values()))==127 and not set(terms)&set(names.values())
 assert names[237]=='LMPW' and terms['LM']=='218:0'
 data=json.loads(candidate.read_text());rules={w:(l,r) for w,l,r in data['rules']};assert len(rules)==len(data['rules'])==data['rules_count']
 for w,(l,r) in rules.items():
  assert w==l+r and w not in terms
  for side,c in enumerate((l,r)):
   assert c in rules or c in terms
   if c in terms:assert allowed[c]&(1<<side)
 def project(w,bits):
  for bit in bits:assert w in rules;w=rules[w][int(bit)]
  return w
 routes={(r['source'],r['read']):r['word'] for r in data['routes']};assert len(routes)==len(data['routes'])==11
 symbols=json.loads((fine/'runtime/inputs/semantic-symbols.json').read_text());inv={n:c for c,n in symbols.items()};inverse={w:q for q,w in oldnames.items()};checked=[]
 for c in old['left_entry_projection_constraints']:
  r=c['reason'];key=(r['source'],r['read']);bits=c['prefix'];w=encode(''.join(inv[n] for n in c['word']))
  if r.get('via')==177:bits=str(r['previous'])+bits
  new=word(source['atoms'][oldterms[w]]['ast']) if w in oldterms else names[inverse[w]]
  if key==(218,0) and bits=='00':assert w=='LNPQ';new='L'
  assert project(routes[key],bits)==new,(key,bits,new)
  checked.append(dict(source=key[0],read=key[1],prefix=bits,old_target=w,new_target=new))
 assert checked==meta['route_derivation'] and len(checked)==22
 released={24,89,107,152,154,175,188,207,213,245};roots=[names[q] for q in source['required_entry_roots'] if q not in released]
 for w in roots:assert w in rules
 locks=(fine/'fine-lock54.txt').read_text().splitlines();assert int(locks[0])==len(locks)-1==54
 for w,bit,target in map(str.split,locks[1:]):assert project(w,bit)==target
 fallback={names[q]:tuple(word(i) for i in ast[int(source['sequence_ast_roots'][str(q)])][1:]) for q in names};byast={int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()};visiting=set()
 def join(a,b):return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2])
 @cache
 def astprop(i):
  key=('A',i);assert key not in visiting;visiting.add(key);r=ast[i]
  value=wordprop(byast[i]) if i in byast else (0,0,0) if r[0]=='L' else join(astprop(r[1]),astprop(r[2]));visiting.remove(key);return value
 @cache
 def wordprop(w):
  key=('W',w);assert key not in visiting;visiting.add(key)
  value=astprop(source['atoms'][terms[w]]['ast']) if w in terms else join(*(wordprop(c) for c in (rules[w] if w in rules else fallback[w])));visiting.remove(key);return value
 props=astprop(source['original_ast']);assert not data.get('properties') or list(props)==data['properties'];assert props[1]<=6 and props[2]<=64
 return dict(status='PASS_LM_FINITE_GRAMMAR_AUDIT',grammar_roles=len(rules),retained_framework_roles=117,prospective_total_roles=117+len(rules),route_cases=22,bootstrap_equations=54,properties=list(props),newAX_tokens=len(names[76]),source_AST_changes=meta['source_edits'],source_override=override,route_derivation=checked,candidate_sha256=hashlib.sha256(candidate.read_bytes()).hexdigest(),scope='Exact changed source, grammar, path and local route identities; AX logical equivalence is a separate theorem, and full literal runtime and blank-start verification remains necessary.')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,required=True);p.add_argument('--backend',type=Path,required=True);p.add_argument('--fine',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=audit(a.candidate,a.backend,a.fine);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ('route_derivation','source_override')},indent=2))
