#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-direct-ipra-final-retry';O=D/'research/nine-sharing-sign31-direct-ipra-retry01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'7892c52f793560dcde1e3558741a13b58a3909b066f2555b860d3812c8a063fe','source-manifest.json':'291d66fc47233f2b28ed230d88a9b9909c7765a7c697c3c2f04c32af4a66e81f','framework-survey.py':'c6b9ede1698b1f31a0848d37ffd22940419d16b2b9810e60a25220e3bc1ce8dd','partial-survey.py':'78b966aee13f8cba53c9c359860c7b8f51e7ba2668eb32cc134b5c0a6e2a67f8','seed-data-survey.py':'a19191c2540184166ec49c103a228efb90631d0b17c6bc286c7cf1d4479c514c'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign31DirectPolynomialBridge','Sign31DirectNative','Sign31DirectStandard','Sign31DirectTranslated'];assert [r['module'].split('.')[-1] for r in m]==names
orig=(O/'src/DiophantineConsistency/Sign31DirectIPRA.lean').read_text();terms=['polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence']
def th(s,n):
 m=re.search(r'^theorem '+n+r'\b.*?(?=\n(?:theorem |end DiophantineConsistency\.))',s,re.M|re.S);assert m;return m.group(0).strip()
for row,n,t in zip(m,names,terms):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==row['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports'] and th(orig,t)==th(s,t) and s.count('#print axioms')==1
assert 'abbrev expression := Sign31CurrentExpression.expression' in (P/'src/DiophantineConsistency/Sign31DirectPolynomialBridge.lean').read_text()
s=json.loads((O/'attempt01/state.json').read_text());assert sha(O/'attempt01/state.json')=='cafb98940ef713e8a29aab450bd55472feb7c16f133afb3ecbb6da32a9031aa0' and s['status']=='FAILED' and len(s['rows'])==6 and all(r['compile']['exit']==0 for r in s['rows'][:5]) and s['rows'][5]['compile']['exit']==-6
print(json.dumps({'status':'PASS_STATIC','scope':'four exact theorem bodies split into narrower modules, using five successful rows only'}))
