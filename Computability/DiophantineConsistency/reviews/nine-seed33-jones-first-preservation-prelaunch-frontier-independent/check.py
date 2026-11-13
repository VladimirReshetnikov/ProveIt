#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-first-preservation-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='4716caf053d326bf90ad72a011f5c6651f030b640df6d80593f1b6e687b3e4e8' and sha(P/'source-manifest.json')=='5651f5f1aab18e8c2d3e2aa094f1743d637533ba0a611dd5a4ed8345d0ce6b1d';gen=D/'research/nine-seed33-jones-first-preservation-draft/generate.py';assert sha(gen)=='6ba5b8d4d5e076d2b10bfd7411aa054cc02c2071c1bbb8fa6764eec1c5b006e4'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['module']=='DiophantineConsistency.Sign33FirstPreservation' and m[0]['imports']==['DiophantineConsistency.Sign33MacroPrefixFirst'];p=P/'src/DiophantineConsistency/Sign33FirstPreservation.lean';s=p.read_text();assert sha(p)==m[0]['source_sha256']=='001889150e87deefe92450cbfbe93a3b887b2ce02a86e1c0b53fb12a25208b9a'
a=re.findall(r'change \(Dag.snoc d(\d+) _\).values a \(Fin.castSucc ⟨0, by decide⟩\)',s);b=re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+) _ ⟨0, by decide⟩',s);assert list(map(int,a))==list(map(int,b))==list(range(44,0,-1))
for z in ('d45.values a ⟨0, by decide⟩ = d1.values a ⟨0, by decide⟩','rw [Sign33MacroPrefixes.recipe_eq_named, d45_first_eq_d1]','exact Sign33MacroPrefixFirst.first_prefix_value a'):assert z in s
assert s.count('#print axioms')==2
print(json.dumps({'status':'PASS_STATIC','scope':'44 prefix preservation steps and first recipe entry only; no full output/JSON equality'}))
