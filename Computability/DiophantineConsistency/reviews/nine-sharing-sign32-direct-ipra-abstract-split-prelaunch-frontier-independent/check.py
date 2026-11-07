#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign32-direct-ipra-abstract-split';old=D/'research/nine-sharing-sign32-direct-ipra-abstract-retry/src/DiophantineConsistency';src=p/'src/DiophantineConsistency';sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(p/'run.py')=='5a98db2ab91ce75fc2afdcc638652e750989cb638041718a5b1d113a99906cac' and sha(p/'source-manifest.json')=='34c00d1dee2cd8ed7fe67f8619ee9d5ad9d9264b10594218ce02f8b81403f32b' and sha(p/'partial-survey.py')=='00d919deb9204849c8f403a07d3c9e048ab817afc0ae6faed58e906de498b361'
m=json.loads((p/'source-manifest.json').read_text());names=['Sign32AbstractExpressionDef','Sign32AbstractExpressionEval','Sign32CurrentExpressionDef','Sign32CurrentExpressionEval'];assert [x['module'].split('.')[-1] for x in m['rows']]==names
for row,n in zip(m['rows'],names):
 t=(src/(n+'.lean')).read_text();assert sha(src/(n+'.lean'))==row['source_sha256'];assert [x[7:] for x in t.splitlines() if x.startswith('import ')]==row['imports']
orig=(old/'Sign32AbstractExpression.lean').read_text();d=(src/'Sign32AbstractExpressionDef.lean').read_text();e=(src/'Sign32AbstractExpressionEval.lean').read_text();cut=lambda t,start,end:t[t.index(start):t.index(end,t.index(start))].strip();assert cut(orig,'def expression','theorem eval_expression')==cut(d,'def expression','end DiophantineConsistency')
assert cut(orig,'theorem eval_expression','end DiophantineConsistency')==cut(e,'theorem eval_expression','end DiophantineConsistency')
orig2=(old/'Sign32CurrentExpressionDef.lean').read_text();d2=(src/'Sign32CurrentExpressionDef.lean').read_text();assert cut(orig2,'attribute [local irreducible]','end DiophantineConsistency')==cut(d2,'attribute [local irreducible]','end DiophantineConsistency')
t=(src/'Sign32CurrentExpressionEval.lean').read_text();assert 'exact Sign32AbstractExpression.eval_expression CurrentWindowCarry2011.ports w' in t and 'Fin.cons (1 : V) w i' in t
print(json.dumps({'status':'PASS_STATIC','stages':4,'scope':'source split and fixed-port evaluation only; no endpoint or JSON claim'}))
