#!/usr/bin/env python3
import collections,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-circuit-draft';n=root/'research/nine-sharing-sign14-positive74-syntax-check/src/DiophantineConsistency';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();s=(p/'Sign14Positive74Circuit.lean').read_text();prov=json.loads((p/'source-inputs.json').read_text());seed=root/'research/nine-sharing-sign14-positive74-candidate/seed.json';assert sha(seed)=='10d4e4739d5e6657cc43ea71792c363bf0e292fd65f0cf11372fd20b4b5de15b'
for f,h in prov['node_sources'].items():assert sha(n/f)==h
# Parse all declared nodes and decode their operands independently.
pattern=re.compile(r'^def g(\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) := \((.+?)\) ([+*\-]) \((.+)\)$',re.M)
def operand(x):
 m=re.fullmatch(r'g(\d\d) p',x)
 if m:return ('reg',int(m[1]))
 m=re.fullmatch(r'Expr.var (\d+)',x)
 if m:return ('var',int(m[1]))
 m=re.fullmatch(r'Expr.constant \(p (\d+)\)',x)
 if m:return ('port',int(m[1]))
 m=re.fullmatch(r'Expr.constant (\d+)',x)
 if m:return ('lit',int(m[1]))
 raise ValueError(x)
ops={'+':'add','-':'sub','*':'mul'};nodes={}
for f in sorted(prov['node_sources']):
 text=(n/f).read_text();matches=pattern.findall(text);assert len(matches)==len(re.findall(r'^def g\d\d\b',text,re.M))
 for i,a,o,b in matches:assert int(i) not in nodes;nodes[int(i)]=(ops[o],operand(a),operand(b))
assert set(nodes)==set(range(65))
body=s.split('def gates : List Gate := [',1)[1].split(']',1)[0];matches=re.findall(r'⟨\.(add|sub|mul), \.(var|port|lit|reg) (\d+), \.(var|port|lit|reg) (\d+)⟩',body);assert body.count('⟨')==74==len(matches)
gates=[(o,(a,int(x)),(b,int(y))) for o,a,x,b,y in matches];assert gates[:65]==[nodes[i] for i in range(65)]
roots=(23,41,48,61,64);assert gates[65:70]==[('mul',('reg',j),('reg',j)) for j in roots] and gates[70:]==[('add',('reg',65),('reg',66)),('add',('reg',70),('reg',67)),('add',('reg',71),('reg',68)),('add',('reg',72),('reg',69))]
expr=(n/'Sign14Positive74Expression.lean').read_text()
for i,j in enumerate(roots):assert f'def row{i:02} (p : Fin 4 → ℤ) : Expr (Fin 14) := (g{j:02} p)' in expr
assert 'row00 p * row00 p + row01 p * row01 p + row02 p * row02 p +\n    row03 p * row03 p + row04 p * row04 p' in expr
parents=json.loads('['+s.split('def parents : List ℕ := [',1)[1].split(']',1)[0]+']');assert parents==prov['parents'] and len(parents)==74
counts=collections.Counter(g[0] for g in gates);assert dict(counts)==prov['counts']=={'add':18,'sub':18,'mul':38};used=set()
for i,(_,a,b) in enumerate(gates):
 for t,j in (a,b):
  assert (t!='reg' or j<i) and (t!='var' or j<14) and (t!='port' or j<4)
for i in range(73):
 par=parents[i];assert i<par<74 and ('reg',i) in gates[par][1:]
stack=[73]
while stack:
 i=stack.pop()
 if i in used:continue
 used.add(i);stack.extend(j for typ,j in gates[i][1:] if typ=='reg')
assert used==set(range(74))
# Independently expand each register to the external candidate AST.
ports=['beta','K0','MC','MF'];memo=[]
def get(x):
 typ,i=x
 return {'reg':lambda:memo[i],'var':lambda:('var',i+1),'port':lambda:('port',ports[i]),'lit':lambda:('num',i)}[typ]()
for op,a,b in gates:memo.append((op,get(a),get(b)))
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
ext=json.loads(seed.read_text());rs=[tup(row['expr']) for row in ext['residuals']];assert [memo[i] for i in roots]==rs and ext['output']=='sum of squares of five listed residuals'
expected=('mul',rs[0],rs[0])
for x in rs[1:]:expected=('add',expected,('mul',x,x))
assert memo[73]==expected
for f in ('nine-sharing-sign14-positive74-candidate-independent','nine-sharing-sign14-positive74-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_AUDIT','source_sha256':sha(p/'Sign14Positive74Circuit.lean'),'gate_count':74,'counts':dict(counts),'parent_edges':73,'scope':'source structural/topological/live graph match; Lean compilation, evaluator semantics, PDF and external-file theorem remain separate'},indent=2))
