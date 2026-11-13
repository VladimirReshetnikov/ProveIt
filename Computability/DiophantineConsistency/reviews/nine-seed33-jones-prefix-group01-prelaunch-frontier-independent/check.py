#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group01-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='c82161a9d2a76f8d595a57a980530f80579523c3e106b71c2f0f6e37dbd9f8dc' and sha(P/'source-manifest.json')=='88df7eaa4d8fdc125369581d5967269e7f2d2adc896a5ed4c6909065c8cd77ed';m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['module']=='DiophantineConsistency.Sign33MacroPrefixGroup01' and m[0]['imports']==['DiophantineConsistency.Sign33MacroPrefixFirst'];p=P/'src/DiophantineConsistency/Sign33MacroPrefixGroup01.lean';s=p.read_text();assert sha(p)==m[0]['source_sha256']=='4de34e34ba44e50597c0bd4acdc6e72ed32ee06a344bec2afe1ab87da3173d17'
b=D/'research/nine-seed38-jones-prefix-group01-retry01/src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean';assert sha(b)=='07df9f3ac1f7fa7d6c02241385d81added00c92994060dcfb9070a99ce871cd9' and b.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34')==s
prefix=(D/'research/nine-seed33-jones-named-prefix-check/src/DiophantineConsistency/Sign33MacroPrefixes.lean').read_text()
for x in ('def d2 : Dag 2 := .snoc d1 (.pow (.ref ⟨0, by decide⟩) (.lit 5))','def d3 : Dag 3 := .snoc d2 (.pow (.ref ⟨1, by decide⟩) (.pow (.lit 5) (.lit 34)))','def d4 : Dag 4 := .snoc d3 (.pow (.ref ⟨2, by decide⟩) (.lit 16))'):assert x in prefix
for x in ('theorem prefix_B','theorem prefix_q','theorem prefix_N','5 ^ 34'):assert x in s
assert s.count('#print axioms')==3
print(json.dumps({'status':'PASS_STATIC','scope':'symbolic short-prefix B/q/N only, no full recipe equality'}))
