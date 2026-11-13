#!/usr/bin/env python3
"""Check explicit Lean rows, selected graph provider and receipt; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-explicit-rows-binding';O=P/'observations/attempt01';S=P/'DisplayedRows.lean';G=D/'research/ten-positive-80-original-kernel-variant/equation.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
t=json.loads((O/'terminal.json').read_text());source=S.read_text();graph=json.loads(G.read_text());assert t['exit']==0 and t['reason'] is None
assert sha(S)==sha(O/'source.txt')==t['source_sha256']=='fd36492f39119d761fb23adf835bc922c8e8ed092aed7e1ec88aac7b4844c585' and sha(P/'run.py')==t['runner_sha256']=='a6eca372ba8dc7f091bb926c221d62a7e782f231af2053e1f04b373657d9e839'
assert not re.search(r'\b(?:sorry|admit)\b',source) and sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256']
logs=(O/'stdout').read_text()+(O/'stderr').read_text();assert logs.count("'TenPositive80DisplayedRows.output_eq' depends on axioms: [propext]")==1 and not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
obj=Path(t['output_root'])/'DisplayedRows.olean';assert sha(obj)==t['object_sha256']=='aeafe96a70f42a594e30adaf5397289b5155c98c6d481fcdf4e8bffc30956eff'
direct=next(Path(x)/'Direct80Graph.olean' for x in t['lean_path'].split(':') if (Path(x)/'Direct80Graph.olean').is_file());assert str(direct)==t['graph']['path'] and sha(direct)==t['graph']['sha256']=='95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4'
union=Path('/tmp/direct80-coherent-rebuild-2fbk3sj_/lib/Direct80Graph.olean');assert sha(union)==sha(direct)
assert re.findall(r'^  let ([a-j]) : Expr \(Fin 10\) := \.var (\d+)$',source,re.M)==[(v,str(i)) for i,v in enumerate('abcdefghij')]
assert re.findall(r'^  let (port\d) : Expr \(Fin 10\) := \.constant \(p (\d+)\)$',source,re.M)==[(f'port{i}',str(i)) for i in range(4)]
rows=re.findall(r'^  let (r\d\d) := (\w+) ([+*\-]) (\w+)$',source,re.M);assert len(rows)==80 and len(graph['source'])==80
refs=dict(zip(graph['witnesses'],'abcdefghij'));refs.update(dict(zip(graph['fixed_numerals'],[f'port{i}' for i in range(4)])))
for i,((name,op,x,y),(reg,a,rop,b)) in enumerate(zip(graph['source'],rows),1):
 f=lambda k: str(k) if isinstance(k,int) else refs[k]
 assert (reg,a,rop,b)==(f'r{i:02d}',f(x),op,f(y));refs[name]=reg
assert refs[graph['output']]=='r80' and '  r80\n\ntheorem output_eq' in source
assert 'theorem output_eq (p : Fin 4 → ℤ) : output_by_rows p=(graph p).output := by rfl' in source
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ten-positive-80-decimal-display-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS 80 Lean registers and slots vs JSON; reviewed display checker independently matches TeX/PDF and payload bytes')
print('selected direct graph',direct,sha(direct),'fresh union graph identical bytes',union)
print('source',sha(S),'object',sha(obj),'terminal',sha(O/'terminal.json'))
print('No Lean replay or formal external file/coefficient semantics; provider transitive ancestry inherited')
