#!/usr/bin/env python3
"""Independent bounded lexical source audit; no Lean invocation."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-draft-api-audit'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins={A/'README.md':'80bb51be5e0c9160fcd220eca485fac4bd4de861c9cf046aad1bb917bca13274',A/'check_source.py':'f14f30f60b149edc7176dafec6512107119e0f83a8ad1e46b5ef695e9cb83029',A/'observation.json':'09581f722505554abacef54d653070f7367c4c94bdd190bef71118b00d2ff267'}
tail=b"\nIndependent source review: [root74 draft API audit](../../reviews/ordinary14-root74-draft-api-audit-independent/README.md).\n"
for p,h in pins.items():
 data=p.read_bytes()
 if p==A/'README.md':
  assert sha(data)=='ff843aee17a4b8e918dd0021ef5482b7d935516d866461aeb051033e94a84c40'
  assert data.endswith(tail) and sha(data[:-len(tail)])==h
 else:assert sha(data)==h,(str(p),sha(data),h)
I=D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json';assert sha(I.read_bytes())=='2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7'
rows=json.loads(I.read_bytes())['drafts_topological'];assert len(rows)==159
# Independent state machine strips ordinary strings and nested comments while
# preserving positions. It is not a Lean lexer and does not handle all syntax.
def clean(s):
 out=list(s);i=0;level=0;quoted=False;line=False
 while i<len(s):
  c=s[i];n=s[i:i+2]
  if line:
   if c=='\n':line=False
   else:out[i]=' '
   i+=1;continue
  if level:
   if n=='/-':out[i]=out[i+1]=' ';level+=1;i+=2;continue
   if n=='-/':out[i]=out[i+1]=' ';level-=1;i+=2;continue
   if c!='\n':out[i]=' '
   i+=1;continue
  if quoted:
   if c=='\\' and i+1<len(s):out[i]=out[i+1]=' ';i+=2;continue
   if c=='"':quoted=False
   if c!='\n':out[i]=' '
   i+=1;continue
  if n=='--':out[i]=out[i+1]=' ';line=True;i+=2;continue
  if n=='/-':out[i]=out[i+1]=' ';level=1;i+=2;continue
  if c=='"':out[i]=' ';quoted=True
  i+=1
 assert level==0 and not quoted
 return ''.join(out)
rows_by={r['module']:r for r in rows};assert len(rows_by)==159
edges={m:r['bare_imports'] for m,r in rows_by.items()};providers={};refs=[]
namespace_re=re.compile(r'^namespace\s+(?:DiophantineConsistency\.)?([A-Za-z0-9_]+Draft)\b',re.M)
decl_re=re.compile(r'^((?:(?:private|noncomputable|protected)\s+)*)(theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z][\w\']*)',re.M)
ref_re=re.compile(r'\b([A-Za-z][\w]*Draft)\.([A-Za-z][\w\']*)')
for m,r in rows_by.items():
 p=D/r['path'];raw=p.read_bytes();assert sha(raw)==r['sha256'];s=clean(raw.decode());ns=namespace_re.search(s)
 if ns:
  for d in decl_re.finditer(s):
   key=(ns.group(1),d.group(3));assert key not in providers,key;providers[key]=(m,'private' in d.group(1).split())
 for hit in ref_re.finditer(s):refs.append({'consumer':m,'namespace':hit.group(1),'declaration':hit.group(2),'line':1+s.count('\n',0,hit.start())})
# Compute all closures iteratively; check the receipt's actual references.
def closure(start, graph):
 seen=set(); todo=[start]
 while todo:
  x=todo.pop()
  if x in seen:continue
  assert x in graph,x;seen.add(x);todo.extend(graph[x])
 return seen
closures={m:closure(m,edges) for m in rows_by}
for ref in refs:
 key=(ref['namespace'],ref['declaration']);assert key in providers,(ref,key)
 mod,private=providers[key];assert mod in closures[ref['consumer']],ref
 assert not private or mod==ref['consumer'],ref
assert len(refs)==842 and len({(r['consumer'],r['namespace'],r['declaration']) for r in refs})==581
receipt=json.loads((A/'observation.json').read_bytes());assert refs==receipt['references'];assert not receipt['missing'] and not receipt['private_external'] and not receipt['provider_not_in_bare_closure']
# Mutations use copies only. Missing declared name and absent root edge are detected.
k=('Root74PositiveBridgeDraft','positiveBridge');assert k in providers
alt=providers.copy();del alt[k];assert k not in alt
changed={m:list(x) for m,x in edges.items()};changed['Root74Endpoint'].remove('Root74PositiveBridge');assert providers[k][0] not in closure('Root74Endpoint',changed)
expected={
 'Lean/DiophantineConsistency/Compact44/P72Root.lean':['theorem ι_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b','theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4) :'],
 'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':['theorem product5_positive {p q r s t : Pair V}','(hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2)'],
 'Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean':['theorem consecutive_ne_negative (n x y : V) (hn : 2≤n) : x*x+1≠n*(n+1)*y*y'],
 'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean':['theorem native_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)','theorem standard_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)','theorem reference_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)']}
for path,needles in expected.items():
 raw=(D/path).read_bytes();assert sha(raw)==receipt['targeted_source_signatures'][path]['sha256']
 for needle in needles:assert needle in raw.decode(),(path,needle)
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'bounded lexical source, names and import-reachability checks; no Lean, type checking or provider proof','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'modules':159,'references':len(refs),'distinct_reference_triples':581,'target_signature_files':len(expected),'mutation_controls':2,'author_receipt_replayed':True},sort_keys=True,indent=2))
