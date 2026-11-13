#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-lean-specialized-draft';Q=D/'research/nine-seed33-jones-compact-macro-prototype/recipe.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'Sign33MacroLanguage.lean':'de51ea7d49bbf72cb046f50b8000027bf723a59e4d54ae17368ee7490da7e864','Sign33MacroRecipe.lean':'c19d0ba99c7594611088744f7c293ac1a7647f4aeb3facd3169e9619d0152ad1','build_language.py':'fc308545cf4cbaf6566f126c402644b26fce5a738afe0aba321a274b346eec18','quote.py':'0036ca4c0acec17181d1cee90c76a3397988ef085069a5cf28fcffaf78c9f914'}.items():assert sha(P/n)==h
assert sha(Q)=='06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3';base=D/'research/nine-seed38-jones-compact-language-retry01/src/DiophantineConsistency/Norm38MacroLanguage.lean';assert sha(base)=='8b25a5ac8047503064f7d044c0d17f36f39b458902b8e927c8ec685fc8677b3f'
s=base.read_text()
for x,y in [('Norm38NamedFormula','Sign33NamedFormula'),('Norm38MacroLanguage','Sign33MacroLanguage'),('SharingSeed38','SharingSeed33'),('Fin 39','Fin 34'),('Fin 40','Fin 35'),('codingExpo 38 4','codingExpo 33 4'),('codingStar 38 4','codingStar 33 4')]:assert x in s;s=s.replace(x,y)
assert s==(P/'Sign33MacroLanguage.lean').read_text() and '38' not in s
r=json.loads(Q.read_text());assert len(r['nodes'])==45 and r['inputs']==9 and r['output']=='output';lookup={}
def ne(e):
 op=e[0]
 if op=='lit':return f'(.lit {e[1]})'
 if op=='index':assert e[1]=='r';return '(.index)'
 if op=='expo':assert e[1]=='k';return '(.expo)'
 assert op in ('add','sub','mul','pow');return f'(.{op} {ne(e[1])} {ne(e[2])})'
def rt(e):
 op=e[0]
 if op=='const':return f'(.constant ({e[1]} : Int))'
 if op=='var':assert 0<=e[1]<9;return f'(.input ⟨{e[1]}, by decide⟩)'
 if op=='ref':assert e[1] in lookup;return f'(.ref ⟨{lookup[e[1]]}, by decide⟩)'
 if op=='fixed':assert e[1] in ('z','y');return '(.fixedZ)' if e[1]=='z' else '(.fixedY)'
 if op=='pcoef':assert e[1]=='k';return '(.pcoef)'
 if op in ('add','sub','mul'):return f'(.{op} {rt(e[1])} {rt(e[2])})'
 if op=='pow':return f'(.pow {rt(e[1])} {ne(e[2])})'
 if op=='sum_range':assert e[1]=='r';return f'(.sumRange {ne(e[2])} {rt(e[3])})'
 if op=='sum_star':assert e[1]=='k';return f'(.sumStar {rt(e[2])})'
 raise AssertionError(e)
t=(P/'Sign33MacroRecipe.lean').read_text();lines=[x for x in t.splitlines() if re.match(r'  let d\d+ : Dag \d+ := \.snoc ',x)];assert len(lines)==45
for i,node in enumerate(r['nodes']):
 assert node['name'] not in lookup
 assert lines[i]==f'  let d{i+1} : Dag {i+1} := .snoc d{i} {rt(node["expr"])}'
 lookup[node['name']]=i
assert lookup['output']==44 and 'def WellScopedTarget : Prop := recipe.scoped = true' in t and 'def SemanticTarget : Prop :=' in t and 'recipe.values a (Fin.last 44) = Sign33IPRAEndpoint.expression.evalRing a' in t and not re.search(r'^(?:theorem|lemma)\b',t,re.M)
for script in ('build_language.py','quote.py'):
 x=subprocess.run([sys.executable,'-I','-S','-B',str(P/script),'--check'],check=True,capture_output=True,timeout=30);assert not x.stderr and json.loads(x.stdout)['status'].startswith('PASS_')
print(json.dumps({'status':'PASS_SOURCE_ONLY','nodes':45,'scope':'sign38 specialization and JSON-to-source quotation checked externally; no Lean parser, boolean scopedness or semantic theorem'},indent=2,sort_keys=True))
