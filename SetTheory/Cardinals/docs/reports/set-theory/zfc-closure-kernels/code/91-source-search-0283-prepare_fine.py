#!/usr/bin/env python3
"""Translate the routed dictionary to exact finest closed AST words.

The frozen source grammar is an input, not an axiom. Closedness and expansions
are rederived from the source AST. The resulting terminal words have variable
length. This lets a search change atom boundaries while sharing exact effects.
"""
from functools import cache
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'machine_reduction/base/zfc245-proof-20261018'
source = json.loads((BASE/'reference/grammar/closed-sequence-grammar-next22.json').read_text())
symbols = json.loads((BASE/'reference/grammar/semantic-symbols.json').read_text())
ast = source['ast_dag']

@cache
def bounds(i):
    r=ast[i]
    if r[0]=='L':
        op,*args=r[1]
        return (1,0) if op=='dec' else (args[0],0) if op=='brk' else (0,args[0]) if op=='cont' else (0,0)
    a,b=map(bounds,r[1:])
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)

@cache
def finest(i):
    r=ast[i]
    return finest(r[1])+finest(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)

atom_tokens={c:finest(source['atoms'][name]['ast']) for c,name in symbols.items()}
assert all(bounds(source['atoms'][name]['ast'])==(0,0) for name in symbols.values())
tokens=sorted(set(x for w in atom_tokens.values() for x in w))
alphabet='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
assert len(tokens)<=len(alphabet)
token_to_char={t:alphabet[k] for k,t in enumerate(tokens)}
atom_words={c:''.join(token_to_char[t] for t in w) for c,w in atom_tokens.items()}
assert len(set(atom_words.values()))==len(atom_words)==44

def encode(word):
    return ''.join(atom_words[c] for c in word)

text=(BASE/'inputs/state_reduction/route-grammar.txt').read_text().splitlines()
nr,nroots,na=map(int,text[0].split())
out=[text[0]]
for line in text[1:1+nr]:
    k,w,q=line.split();k=int(k)
    out.append(f'{len(encode(w[:k]))} {encode(w)} {q}')
out += [encode(w) for w in text[1+nr:1+nr+nroots]]
out += [f'{encode(c)} {mask}' for c,mask in map(str.split,text[1+nr+nroots:])]
(HERE/'fine-grammar.txt').write_text('\n'.join(out)+'\n')

text=(BASE/'inputs/state_reduction/route-constraints.txt').read_text().splitlines()
out=[text[0]];n=int(text[0]);p=1
for _ in range(n):
    src,bit,w,nc=text[p].split();p+=1
    out.append(f'{src} {bit} {encode(w)} {nc}')
    for _ in range(int(nc)):
        b,w=text[p].split();p+=1;out.append(f'{b} {encode(w)}')
ne,orig,na=map(int,text[p].split());out.append(text[p]);p+=1
for _ in range(ne):
    row=text[p].split();p+=1
    out.append('W '+encode(row[1]) if row[0]=='W' else ' '.join(row))
for _ in range(na):
    c,i=text[p].split();p+=1;out.append(f'{encode(c)} {i}')
assert p==len(text)
(HERE/'fine-constraints.txt').write_text('\n'.join(out)+'\n')

text=(BASE/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()
out=[text[0]]+[f'{encode(w)} {b} {encode(t)}' for w,b,t in map(str.split,text[1:])]
(HERE/'fine-lock54.txt').write_text('\n'.join(out)+'\n')

g=json.loads((BASE/'grammar.json').read_text())
fine_rules=[[encode(w),encode(a),encode(b)] for w,a,b in g['rules']]
assert all(w==a+b for w,a,b in fine_rules)
assert not (set(w for w,a,b in fine_rules)&set(atom_words.values()))
out=[str(len(fine_rules))]+[f'{len(a)} {w}' for w,a,b in fine_rules]
out+=[str(len(g['routes']))]+[encode(r['word']) for r in g['routes']]
(HERE/'fine-resume128.txt').write_text('\n'.join(out)+'\n')

names={int(q):''.join({v:k for k,v in symbols.items()}[v] for v in w) for q,w in source['flattened_semantic_words'].items()}
mapping=dict(atom_words=atom_words,token_to_ast={c:t for t,c in token_to_char.items()},
    old_names={str(q):w for q,w in names.items()},fine_names={str(q):encode(w) for q,w in names.items()},
    source_sha256=hashlib.sha256((BASE/'reference/grammar/closed-sequence-grammar-next22.json').read_bytes()).hexdigest(),
    baseline_grammar_sha256=hashlib.sha256((BASE/'grammar.json').read_bytes()).hexdigest())
(HERE/'fine-map.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(json.dumps(dict(status='PASS_EXACT_FINE_TRANSLATION',fine_tokens=len(tokens),atoms=len(atom_words),
    starting_rules=len(fine_rules),source_ast_nodes=len(ast),
    old_AX_length=len(names[76]),fine_AX_length=len(encode(names[76])),
    maximum_atom_length=max(map(len,atom_words.values()))),indent=2))
