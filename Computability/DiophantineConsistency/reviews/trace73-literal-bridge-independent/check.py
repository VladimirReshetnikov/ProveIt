from pathlib import Path
from hashlib import sha256
import json,re
h=Path('research/trace73-literal-bridge');src=h/'Trace73Literal.lean';candidate=Path('research/trace73-center-probe/candidate.json');o=h/'observations/attempt01';ext=h/'observations/rows01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='e16530fbc176faa93f7186dba238c8af5584491d4d08cc87f7bf9771fba1fb64';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(h/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='e4bbe335d32f1f50ed2bfe2440c37f19a1f34ae4def4ff476b6e0778dfc3654d'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Trace73Literal.literal_eq' depends on axioms: [propext]","'Trace73Literal.parent_substitution' depends on axioms: [propext]"] and not (o/'stderr').read_text()
e=json.loads((ext/'terminal.json').read_text());assert sha(ext/'terminal.json')=='4e68e8e69c257d5040f8cc3e4cc2330102b3e1276479d704fe07880a8b150a1d' and e['status']=='PASS' and e['exit']==0 and e['checker_sha256']==e['checker_after']==sha(h/'check_rows.py')
for s in ['stdout','stderr']:assert sha(ext/s)==e[s+'_sha256']
assert not (ext/'stderr').read_text()
g=json.loads(candidate.read_text());rows=g['source'];assert len(rows)==73 and sha(candidate)=='c83151606214c211993fa0c5b9913abae3b6bcf2b00af107e599e4855f936ca6'
code=src.read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Trace73CenterV2'] and '[CommRing R]' in code and 'rw [Trace73Center.substitution, literal_eq]' in code and not re.search(r'\b(sorry|admit)\b',code)
lines=[x.strip() for x in code.splitlines() if x.strip().startswith('let g')];assert len(lines)==73
# Map each JSON operand to its known literal Lean spelling without using the author's parser.
names={x:f'(v {i})' for i,x in enumerate(g['witnesses'])};names.update({x:f'(p {i})' for i,x in enumerate(g['fixed_numerals'])})
for i,(name,op,a,b) in enumerate(rows,1):
 def render(x):return str(x) if type(x) is int else names[x]
 assert lines[i-1]==f'let g{i:02} := {render(a)} {op} {render(b)}',(i,lines[i-1]);names[name]=f'g{i:02}'
assert names[g['output']]=='g73' and re.search(r'^  g73$',code,re.M)
assert 'graph73 p v = Trace73Center.value73 p v := by\n  rfl' in code and 'value75 p (Trace73Center.lift p v) = graph73 p v' in code
print('PASS: exact 73 literal operations/operands/inputs/output independently compared to external JSON; actual arbitrary-ring definitional and parent substitution Lean theorem sources/receipt checked.')
print('JSON parsing remains external; positivity, positive-zero equivalence, iPRA, file binding and transitive provenance remain open.')
