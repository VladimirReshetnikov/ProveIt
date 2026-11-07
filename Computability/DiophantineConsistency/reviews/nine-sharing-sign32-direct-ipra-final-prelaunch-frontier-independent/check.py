#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-final-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'911f7cbc5ead587cd97d1335606aaf76681348d1fd744d7c90a0a87965b273bc','source-manifest.json':'578f875cf5b08f1d557b81358c4da8eaa07257ca57c4a5bcf8f9279071d66fe5','framework-survey.py':'5a43ad29d703539918df3382fa4270e451495cb1924be72c977374da5fee81c5'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign32CurrentExpressionSource','Sign32DirectIPRA'];assert [r['module'].split('.')[-1] for r in m]==names
for r,n in zip(m,names):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==r['imports']
a=(P/'src/DiophantineConsistency/Sign32CurrentExpressionSource.lean').read_text();b=(P/'src/DiophantineConsistency/Sign32DirectIPRA.lean').read_text()
for x in ('Fin 32 → V','Fin 14 → V','Fin.cons (1 : V) w','simp only [internalZero_iff, eval_expression]','hleft.trans Sign32CurrentSourceIff.seed_exists_iff_source'):assert x in a
for x in ('abbrev expression := Sign32CurrentExpression.expression','theorem polynomialBridge','theorem native_equivalence','theorem standard_equivalence','theorem standard_translated_equivalence','not_congr (Sign32CurrentExpression.zero_iff_current (V := V))','IPRAExpressionNative.equivalence_of_bridge','IPRAStandardTheory.provable_iff','IPRABoundedRhoZFC.zfcEquiv'):assert x in b
assert b.count('#print axioms')==4 and a.count('#print axioms')==1
print(json.dumps({'status':'PASS_STATIC','scope':'32-coordinate direct iPRA proposal, fixed ports; no Jones reduction, Lean degree or JSON claim'}))
