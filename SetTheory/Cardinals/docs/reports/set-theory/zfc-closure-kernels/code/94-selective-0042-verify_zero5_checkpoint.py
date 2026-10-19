#!/usr/bin/env python3
"""Independently verify the retained unsuccessful grammar and five-zero score."""
from pathlib import Path
from functools import lru_cache
import json,os,sys
HERE=Path(__file__).resolve().parent
REFERENCE=Path(os.environ.get('ZFC245_REFERENCE',str(HERE.parent/'packages/zfc245-proof-20261018'))).resolve()
sys.path.insert(0,str(REFERENCE/'code'))
import audit_routing_grammar as checker
# The inherited checker formats its output path relative to BASE. Its input
# constants INPUTS and TABLE are already absolute and stay at the reference.
# Only this output-path base changes, to permit an external candidate file.
checker.BASE=HERE.parent
candidate=HERE/'zero5-710418.json'
audit=checker.audit(candidate,short_scan=True)
source=json.loads((REFERENCE/'inputs/closed-sequence-grammar-next22.json').read_text())
symbols=json.loads((REFERENCE/'inputs/semantic-symbols.json').read_text())
encode={name:c for c,name in symbols.items()}
data=json.loads(candidate.read_text())
rules={w:(a,b)for w,a,b in data['rules']}
words={int(q):''.join(encode[c]for c in row)for q,row in source['flattened_semantic_words'].items()}
by_ast={int(a):words[int(q)]for q,a in source['sequence_ast_roots'].items()}
# The original semantic input retains all fallback cuts, including terminal
# children whose state is not a sequence root.
old_rules={}
lines=(REFERENCE/'inputs/semantic.txt').read_text().splitlines();n=int(lines[0].split()[0])
for line in lines[1:n+1]:
    cut,w,state=line.split();cut=int(cut);old_rules[w]=(w[:cut],w[cut:])
def join(a,b):return(1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3]+int(1+a[0]>5))
@lru_cache(None)
def ast(a):
    if a in by_ast:return word(by_ast[a])
    row=source['ast_dag'][a]
    return(0,0,0,0)if row[0]=='L'else join(ast(row[1]),ast(row[2]))
@lru_cache(None)
def word(w):
    if len(w)==1:return ast(source['atoms'][symbols[w]]['ast'])
    a,b=rules[w]if w in rules else old_rules[w]
    return join(word(a),word(b))
properties=ast(source['original_ast'])
assert properties==(3,6,45,11)
assert len(rules)==132 and audit['grammar_states']==132
audit['five_zero_properties']=list(properties)
audit['five_zero_objective']=len(rules)+0.25*properties[3]
audit['sub245_target_met']=False
audit['scope']='Finite grammar and local routing check plus independent score calculation. No candidate machine proof; zero-five target is not met.'
(HERE/'zero5-checkpoint-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({k:audit[k]for k in ['status','grammar_states','five_zero_properties','five_zero_objective','sub245_target_met']},indent=2))
