"""Fresh data-only validation of the supplied finite source bisimulation.

Does not import or run downloaded programs. The two semantics are interpreted
with strings and integer arithmetic by this independently authored checker.
This verifies the supplied AST/certificate relation, independently binds its
original tree to the Coq source table, and does not prove binary runtime.
"""
if not __debug__:
    raise RuntimeError('Assertions are required; do not use python -O or PYTHONOPTIMIZE')

from pathlib import Path
from functools import lru_cache
from collections import Counter
import json, re, hashlib, os
PACKAGE=Path(__file__).resolve().parent.parent
R=Path(os.environ.get('B245_OUTPUT',PACKAGE/'results'))
R.mkdir(parents=True,exist_ok=True)
S=Path(os.environ.get('B245_INPUTS',PACKAGE/'inputs'))
source=json.loads((S/'inputs__closed-sequence-grammar-next22.json').read_text())
grammar=json.loads((S/'candidate-routing245/grammar.json').read_text())
symbols=json.loads((S/'inputs__semantic-symbols.json').read_text())
inverse={v:k for k,v in symbols.items()}
names={int(k):''.join(inverse[v] for v in word) for k,word in source['flattened_semantic_words'].items()}
rules={w:(a,b) for w,a,b in grammar['rules']}
assert len(rules)==128
for w,(a,b) in rules.items():
    assert w==a+b and a and b
    assert all(len(x)==1 or x in rules for x in (a,b))
by_ast={int(ast):names[int(state)] for state,ast in source['sequence_ast_roots'].items()}

@lru_cache(None)
def tree(ast,new):
    if new and ast in by_ast and by_ast[ast] in rules:
        return word_tree(by_ast[ast])
    node=source['ast_dag'][ast]
    if node[0]=='L': return tuple(node[1])
    assert node[0]=='N'
    return (tree(node[1],new),tree(node[2],new))

@lru_cache(None)
def word_tree(word):
    if len(word)==1: return tree(source['atoms'][symbols[word]]['ast'],True)
    a,b=rules[word]
    return (word_tree(a),word_tree(b))

def flatten(node,prefix=''):
    if isinstance(node[0],str): return [(prefix,node)]
    return flatten(node[0],prefix+'0')+flatten(node[1],prefix+'1')

before=flatten(tree(source['original_ast'],False))
after=flatten(tree(source['original_ast'],True))
assert len(before)==len(after)==6460
assert [v for p,v in before]==[v for p,v in after]
# Independently bind the supplied original AST to the actual downloaded Coq
# source table, treating Coq text as inert data and accepting only its finite
# explicit constructor-row grammar.
source_text=(S/'Prog254.v').read_text()
body=re.search(r'Definition p254_tab\s*:\s*list \(cedge \* cedge\)\s*:=\s*\[(.*?)\]\.',source_text,re.S).group(1)
row_pattern=r'\(\s*(CH|C[NIDBC]\s+\d+)\s*,\s*(CH|C[NIDBC]\s+\d+)\s*\)'
rows=re.findall(row_pattern,body)
assert re.sub(row_pattern,'',body).replace(';','').strip()==''
assert len(rows)==6459
coq_op={'CI':'inc','CD':'dec','CB':'brk','CC':'cont','CH':'halt'}
def coq_expand(n,p=''):
    result=[]
    for bit,token in enumerate(rows[n]):
        pieces=token.split();code=pieces[0]
        if code=='CN':
            target=int(pieces[1]);assert n<target<len(rows)
            result.extend(coq_expand(target,p+str(bit)))
        else:
            edge=(coq_op[code],int(pieces[1])) if len(pieces)>1 else (coq_op[code],)
            result.append((p+str(bit),edge))
    return result
assert coq_expand(0)==before
opcodes={'inc':'CI','dec':'CD','brk':'CB','cont':'CC','halt':'CH'}
site_rows=[[p,opcodes[e[0]],e[1] if len(e)>1 else None] for p,e in after]
assert site_rows==json.loads((S/'certificate__sites_logical.json').read_text())
leaves=[dict(before),dict(after)]

@lru_cache(None)
def decode(which,pointer):
    extended=pointer+'0'*64
    for d in range(1,65):
        p=extended[:d]
        if p in leaves[which]: return leaves[which][p],p
    raise AssertionError('Incomplete tree')

def inc(pointer):
    n=len(pointer)
    return format((int(pointer or '0',2)+1)%(1<<n),'0'+str(n)+'b') if n else ''

def cut(pointer,bit,n):
    for _ in range(n):
        i=pointer.rfind(bit)
        if i<0: return ''
        pointer=pointer[:i]
    return pointer

@lru_cache(None)
def segment(which,pointer):
    effects=[0]*9;visited=set()
    while True:
        assert pointer not in visited,'Unterminated fixed segment'
        visited.add(pointer)
        edge,consumed=decode(which,pointer)
        op=edge[0]
        if op in ('dec','halt'): return tuple(effects),pointer
        if op=='inc': effects[edge[1]]+=1; pointer=inc(consumed)
        elif op=='brk': pointer=inc(cut(consumed,'0',edge[1]))
        elif op=='cont': pointer=cut(consumed,'1',edge[1])
        else: raise AssertionError(op)

cert=json.loads((S/'certificate__register_bisimulation.json').read_text())
entries=cert['entries']; assert cert['start_pair']==0
ea,pa=segment(0,''); eb,pb=segment(1,'')
assert ea==eb and entries[0][:2]==[pa,pb]
edges=halts=0
for pa,pb,nz,z in entries:
    a,ca=decode(0,pa);b,cb=decode(1,pb)
    assert a==b
    if a==('halt',):
        assert nz is None and z is None; halts+=1;continue
    assert a[0]=='dec'
    for is_zero,target in [(False,nz),(True,z)]:
        assert type(target)==int and 0<=target<len(entries)
        aa=inc(cut(ca,'0',1)) if is_zero else inc(ca)
        bb=inc(cut(cb,'0',1)) if is_zero else inc(cb)
        va,qa=segment(0,aa);vb,qb=segment(1,bb)
        assert va==vb and entries[target][:2]==[qa,qb]
        edges+=1

# Separate finite projections needed by initialization and special entries.
boot=(S/'inputs__state_reduction__bootstrap-lock54.txt').read_text().splitlines()
assert int(boot[0])==len(boot)-1==54
for line in boot[1:]:
    w,b,child=line.split(); assert rules[w][int(b)]==child
routes={(x['source'],x['read']):x['word'] for x in grammar['routes']}
projections=0
for c in source['left_entry_projection_constraints']:
    reason=c['reason'];key=reason['source'],reason['read']
    bits=c['prefix']
    if key in routes:
        w=routes[key]
        if 'via' in reason: bits=str(reason['previous'])+bits
    else: w=names[c['root']]
    for bit in bits: w=rules[w][int(bit)]
    assert w==''.join(inverse[x] for x in c['word'])
    projections+=1

summary={'scope':'Independent finite data/AST/source-bisimulation audit; not binary runtime proof',
 'working_grammar_rules':len(rules),'instruction_leaves':len(after),
 'ordered_instructions_identical':True,'changed_leaf_addresses':sum(a[0]!=b[0] for a,b in zip(before,after)),
 'maximum_depth':max(len(p) for p,e in after),'maximum_zero_run':max(len(x) for p,e in after for x in p.split('1')),
 'bisimulation_pairs':len(entries),'bisimulation_edges':edges,'halt_pairs':halts,
 'initial_register_increment_counts_match':True,'boot_projection_locks':54,
 'special_entry_projection_cases':projections,'source_certificate_checked':True,
 'original_ast_matches_independent_Coq_source_parse':True,
 'Prog254_source_sha256':hashlib.sha256((S/'Prog254.v').read_bytes()).hexdigest()}
(R/'independent-source-certificate-results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
