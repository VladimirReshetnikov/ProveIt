#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-direct-ipra-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'acf8f183041b96927ded1af5112c0300e475f5b3452f3dcf2f0af2cf9090929c','source-manifest.json':'e2414db104fd4ff01de55a30f408fde4ceb81ff6a5184c82c1b39205834d54b6','partial-survey.py':'78b966aee13f8cba53c9c359860c7b8f51e7ba2668eb32cc134b5c0a6e2a67f8','framework-survey.py':'324fd79cc786f15ebbebd0d28bf4901123571eb850784dff516a8bd36d2211b3'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign31AbstractExpressionDef','Sign31AbstractExpressionEval','Sign31CurrentExpressionDef','Sign31CurrentExpressionEval','Sign31CurrentExpressionSource','Sign31DirectIPRA'];assert [r['module'].split('.')[-1] for r in m]==names;ss=[]
for r,n in zip(m,names):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();ss.append(s);assert sha(p)==r['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==r['imports']
a,b,c,d,e,f=ss
assert 'def expression (p : Fin 4 → ℤ) : Expr (Fin 31)' in a and 'Sign32GenericRemoveInput.removeInput (SharingSeed31Sextic.seed p)' in a
for x in ('w : Fin 31 → V','SharingSeed31Sextic.seed p','Fin.cons (1 : V) w','Sign32GenericRemoveInput.eval_removeInput'):assert x in b
assert 'def expression : Expr (Fin 31)' in c and 'CurrentWindowCarry2011.ports' in c
assert 'w : Fin 31 → V' in d and 'Fin.cons (1 : V) w' in d and 'Sign31AbstractExpression.eval_expression CurrentWindowCarry2011.ports w' in d
for x in ('∃ w : Fin 31 → V','∃ u : Fin 14 → V','Fin.cons (1 : V) w','Sign31CurrentSourceIff.seed_exists_iff_source'):assert x in e
for x in ('abbrev expression := Sign31CurrentExpression.expression','theorem polynomialBridge','ObjectCurrentEquation2011.InternalZero','theorem native_equivalence','theorem standard_equivalence','theorem standard_translated_equivalence','IPRAExpressionNative.equivalence_of_bridge','IPRAStandardTheory.provable_iff','IPRABoundedRhoZFC.zfcEquiv'):assert x in f
assert sum(s.count('#print axioms') for s in ss)==7
print(json.dumps({'status':'PASS_STATIC','scope':'proposed direct Fin31 endpoint, fixed ports; arity-generic substitution, no Jones/Lean degree/JSON binding'}))
