#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group02-staged-check';O=D/'research/nine-seed38-jones-prefix-group02-staged-check/src/DiophantineConsistency';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='4b0234adac6967a02a25fe98ed415f2a4c21dffb78371577b20d1052cfdc68d9' and sha(P/'source-manifest.json')=='cc2c1eafb6fabe1a34089817133479b8e24f5fa9490d6e8014c96d0dcdb73ea9';m=json.loads((P/'source-manifest.json').read_text())['rows'];suffixes=['Carry','E','Ell','Lambda'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroPrefix'+x for x in suffixes]
pins=['7d99a72b7c27c335f4e8c0f2e5a66468c907c8321dce03259a4e13cd456e2d3e','c29dd4f792f6120f11d94cd0ccb1e20524219e01357ade3a3f7e56f970216868','e98e9d78074b1eace78fb798278b7624839d768c0c25717b0e32f78e24277c01','8d81e80eb986a42ede2ab0736bc1d458c4cb73d3b3895b83837a00c480087861'];ss=[]
for row,suf,h in zip(m,suffixes,pins):
 p=P/'src/DiophantineConsistency'/f'Sign33MacroPrefix{suf}.lean';b=O/f'Norm38MacroPrefix{suf}.lean';s=p.read_text();ss.append(s);assert sha(p)==row['source_sha256'] and sha(b)==h and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports'];assert b.read_text().replace('Norm38','Sign33').replace('codingStar 38 4','codingStar 33 4').replace('codingExpo 38 4','codingExpo 33 4').replace('Finset.range 38','Finset.range 33').replace('5 ^ 39','5 ^ 34')==s
assert all('theorem d'+str(i)+'_B' in ss[0] for i in (4,5,6)) and 'codingStar 33 4' in ss[1] and 'codingExpo 33 4' in ss[1] and '5 ^ 34' in ss[1] and 'Finset.range 33' in ss[2] and 'Finset.range (4 * (5 ^ 34 : Nat))' in ss[3]
print(json.dumps({'status':'PASS_STATIC','scope':'symbolic d4-d6 B carry and e/ell/lambda short-prefix values only'}))
