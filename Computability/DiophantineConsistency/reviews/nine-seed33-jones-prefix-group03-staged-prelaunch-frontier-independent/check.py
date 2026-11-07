#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group03-staged-check';O=D/'research/nine-seed38-jones-prefix-group03-staged-check/src/DiophantineConsistency';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='63bb7c33e55687f7c054d4dee524bdd7d8221001ce1873fb99af0439ee2ed0e3' and sha(P/'source-manifest.json')=='9bc2864697c50a35b3a63e56b557d2ff3a8ac37c4c414fd883fe001e6dd35a07';m=json.loads((P/'source-manifest.json').read_text())['rows'];suffixes=['Carry03','Gsmall','Theta','Glarge'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroPrefix'+x for x in suffixes]
pins=['22dc3497bf7c376eb505518e806bec65e98168a77d5185b3f1f331ad192de7ec','a952cf020ba61703f20922f5633b1d3f6fc37d4919f2bfe3933d39b0416bf818','32d162df0a5e6a627b3a2b1f98630a3411bef3f2183cc9974d9687a2f29df5c2','ba80ac2963ba65d8014661cc49f485deed735f772b1cde3fb6906da1ee302653'];ss=[]
for row,suf,h in zip(m,suffixes,pins):
 p=P/'src/DiophantineConsistency'/f'Sign33MacroPrefix{suf}.lean';b=O/f'Norm38MacroPrefix{suf}.lean';s=p.read_text();ss.append(s);assert sha(p)==row['source_sha256'] and sha(b)==h and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports'];assert b.read_text().replace('Norm38','Sign33').replace('5 ^ 38','5 ^ 33')==s
assert all('theorem '+x in ss[0] for x in ('d8_B','d9_B','d9_b')) and 'theorem prefix_g' in ss[1] and 'theorem prefix_theta' in ss[2] and 'theorem prefix_G' in ss[3] and '5 ^ 33' in ss[3]
print(json.dumps({'status':'PASS_STATIC','scope':'symbolic short-prefix carries and g/theta/G only'}))
