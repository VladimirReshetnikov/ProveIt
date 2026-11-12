#!/usr/bin/env python3
"""Lexical namespace/dependency audit of qualified *Draft references; no Lean."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;D=P.parents[1];I=D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(I.read_bytes())=='2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7'
j=json.loads(I.read_bytes());rows=j['drafts_topological'];assert len(rows)==159
# Replace nested comments and ordinary string literals with whitespace while
# preserving newlines. This is a lexical approximation, not Lean's lexer.
def scrub(text):
 out=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif string:
   if text[i]=='\\' and i+1<len(text):out.extend('  ');i+=2
   elif text[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif text.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif text.startswith('--',i):
   k=text.find('\n',i)
   if k<0:out.extend(' '*(len(text)-i));break
   out.extend(' '*(k-i));i=k
  elif text[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(text[i]);i+=1
 assert not depth and not string
 return ''.join(out)
decl_re=re.compile(r'^((?:(?:private|noncomputable|protected)\s+)*)(theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z][\w\']*)',re.M)
ns_re=re.compile(r'^namespace\s+(?:DiophantineConsistency\.)?(\w+Draft)\b',re.M)
ref_re=re.compile(r'\b([A-Za-z][\w]*Draft)\.([A-Za-z][\w\']*)')
providers={};references=[];edges={r['module']:r['bare_imports'] for r in rows};source_hashes={}
for r in rows:
 p=D/r['path'];data=p.read_bytes();assert sha(data)==r['sha256'];source_hashes[r['module']]=r['sha256'];s=scrub(data.decode());ns=ns_re.search(s)
 if ns:
  for mods,kind,name in decl_re.findall(s):
   key=(ns.group(1),name);assert key not in providers,(key,providers.get(key),r['module']);providers[key]={'module':r['module'],'private':'private' in mods.split()}
 for m in ref_re.finditer(s):references.append({'consumer':r['module'],'namespace':m.group(1),'declaration':m.group(2),'line':s.count('\n',0,m.start())+1})
assert len(edges)==159
def reachable(start):
 todo=[start];seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  assert n in edges,n
  seen.add(n);todo.extend(edges[n])
 return seen
closures={m:reachable(m) for m in edges};missing=[];unreachable=[];private_external=[]
for r in references:
 key=(r['namespace'],r['declaration']);provider=providers.get(key)
 if provider is None:missing.append(r);continue
 if provider['module'] not in closures[r['consumer']]:unreachable.append({**r,'provider':provider['module']})
 if provider['private'] and provider['module']!=r['consumer']:private_external.append({**r,'provider':provider['module']})
# Targeted source-signature controls; these do not check Lean elaboration.
checks={
 'Lean/DiophantineConsistency/Compact44/P72Root.lean':['theorem ι_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b','theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4) :'],
 'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':['theorem product5_positive {p q r s t : Pair V}','(hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2)'],
 'Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean':['theorem consecutive_ne_negative (n x y : V) (hn : 2≤n) : x*x+1≠n*(n+1)*y*y'],
 'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean':['theorem native_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)','theorem standard_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)','theorem reference_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)']}
qualified={r['path']:r['sha256'] for r in j['qualified_direct_sources']};targeted={}
for name,needles in checks.items():
 p=D/name;data=p.read_bytes()
 expected=qualified.get(name, {'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d'}.get(name))
 assert expected is not None and sha(data)==expected,(name,sha(data),expected)
 for needle in needles:assert needle in data.decode(),(name,needle)
 targeted[name]={'sha256':sha(data),'snippets':needles}
# Controls ensure a missing declaration and a removed root import are observed.
test_ref=next(r for r in references if r['consumer']=='Root74Endpoint' and r['namespace']=='Root74PositiveBridgeDraft' and r['declaration']=='positiveBridge')
assert providers.get((test_ref['namespace'],test_ref['declaration'])) is not None
without=dict(providers);del without[(test_ref['namespace'],test_ref['declaration'])]
assert (test_ref['namespace'],test_ref['declaration']) not in without
assert 'Root74PositiveBridge' in edges['Root74Endpoint']
without_edges=dict(edges);without_edges['Root74Endpoint']=[x for x in edges['Root74Endpoint'] if x!='Root74PositiveBridge']
def alt_reachable(start):
 todo=[start];seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(without_edges[n])
 return seen
assert providers[(test_ref['namespace'],test_ref['declaration'])]['module'] not in alt_reachable('Root74Endpoint')
print(json.dumps({'scope':'lexical qualified *Draft references only; not Lean parsing, name elaboration, transitive provider or axiom audit','inventory_sha256':sha(I.read_bytes()),'module_count':len(rows),'reference_occurrences':len(references),'distinct_reference_triples':len({(r['consumer'],r['namespace'],r['declaration']) for r in references}),'missing':missing,'provider_not_in_bare_closure':unreachable,'private_external':private_external,'targeted_source_signatures':targeted,'mutation_controls':['removed target declaration detected','removed root import detected'],'sources':source_hashes,'references':references},sort_keys=True,indent=2))
