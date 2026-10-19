"""Independent finite grammar audit and explicit full source-leaf enumeration.

This is not an instruction-table, frame, bootstrap or logical-equivalence proof.
"""
import pathlib,json,hashlib,functools,importlib.util,collections
import os
HERE=pathlib.Path(__file__).resolve().parent
BASE=pathlib.Path(os.environ.get('ZFC245_BASE',str(HERE.parent/'baseline245/zfc245-proof-20261018')))
OUT=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('local_audit',BASE/'code/audit_routing_grammar.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
# Only the checker output's display path changes; frozen INPUTS and TABLE do not.
audit.BASE=OUT.parent
source=json.loads((BASE/'reference/grammar/closed-sequence-grammar-next22.json').read_text())
symbols=json.loads((BASE/'reference/grammar/semantic-symbols.json').read_text())
encode={v:k for k,v in symbols.items()}
names={int(q):''.join(encode[x] for x in ws) for q,ws in source['flattened_semantic_words'].items()}
lines=(BASE/'reference/grammar/semantic.txt').read_text().splitlines();n=int(lines[0].split()[0])
old={w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split,lines[1:n+1])}
@functools.cache
def original(i):
 r=source['ast_dag'][i]
 return ('L',tuple(r[1])) if r[0]=='L' else ('N',original(r[1]),original(r[2]))
def leaves(t,p=''):
 if t[0]=='L':yield p,t[1];return
 yield from leaves(t[1],p+'0');yield from leaves(t[2],p+'1')
baseline=[label for pc,label in leaves(original(source['original_ast']))]
all_results=[]
for filename in ['search-128-1018.json','search-freecold-1018.json','search-semantic-smoke.json','search-semanticdelete-1018.json','search-context2-1018.json','route-ax-470-repaired.json','search-axrouter-1018.json','search-softzero5-c15.json','search-softzero5-c50.json','search-semantic-zero5.json','zero5-repaired.json','zero5-feasibility-best.json','free183-k137.json','search-hardzero5-final.json']:
 p=OUT/filename
 if not p.exists():continue
 d=json.loads(p.read_text());g={q:(a,b) for q,a,b in d['rules']};local_names=dict(names);local_names.update({int(q):w for q,w in d.get('root_word_overrides',{}).items()})
 by_ast={int(ast):local_names[int(q)] for q,ast in source['sequence_ast_roots'].items()}
 @functools.cache
 def ast(i):
  if i in by_ast:return word(by_ast[i])
  r=source['ast_dag'][i]
  return ('L',tuple(r[1])) if r[0]=='L' else ('N',ast(r[1]),ast(r[2]))
 @functools.cache
 def word(w):
  if len(w)==1:return ast(source['atoms'][symbols[w]]['ast'])
  a,b=g.get(w,old.get(w));return ('N',word(a),word(b))
 sites=list(leaves(ast(source['original_ast'])));assert [label for pc,label in sites]==baseline
 maximum=max(max(map(len,pc.split('1'))) for pc,label in sites)
 tailmax=max(len(pc)-len(pc.rstrip('0')) for pc,label in sites)
 assert maximum==tailmax
 bad=[dict(pc=pc,op=label[0],arguments=list(label[1:])) for pc,label in sites if len(pc)-len(pc.rstrip('0'))>=6]
 result=audit.audit(p,short_scan=True)
 result['explicit_leaf_audit']=dict(status='PASS',source_leaves=len(sites),ordered_instruction_labels_unchanged=True,maximum_zero_run=maximum,maximum_trailing_zero_run=tailmax,six_zero_suffix_sites=len(bad),six_zero_suffix_instruction_counts=dict(collections.Counter(x['op'] for x in bad)))
 result['six_zero_suffix_sites']=bad
 (OUT/(p.stem+'-local-audit.json')).write_text(json.dumps(result,indent=2)+'\n')
 all_results.append({k:v for k,v in result.items() if k in ['status','candidate','candidate_sha256','grammar_states','working_states','search_AST_properties','explicit_leaf_audit']})
 print(filename,result['working_states'],maximum,len(bad),flush=True)
(OUT/'independent-audits.json').write_text(json.dumps(all_results,indent=2)+'\n')
