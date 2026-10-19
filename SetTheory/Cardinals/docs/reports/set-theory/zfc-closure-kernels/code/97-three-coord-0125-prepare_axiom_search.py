#!/usr/bin/env python3
"""Prepare a source-preserving dictionary and certified AX-symmetry variants."""
import sys, json, itertools
from pathlib import Path
from functools import lru_cache

HERE=Path(__file__).resolve().parent
REF=HERE/'vendor'
sys.path.insert(0,str(REF/'axiom_symmetry'))
import source_model as sm
source=json.loads((REF/'reference_data/reference/grammar/closed-sequence-grammar-next22.json').read_text())
ast=source['ast_dag']
cm=json.loads((REF/'inputs/canonical-map.json').read_text())
base=json.loads((REF/'candidates/canonical-20262021.json').read_text())
g={w:(a,b)for w,a,b in base['rules']}
ax=max(base['roots'],key=len)

@lru_cache(None)
def bounds(i):
    r=ast[i]
    if r[0]=='L':
        op,*arg=r[1]
        return (1,0) if op=='dec' else (arg[0],0) if op=='brk' else (0,arg[0]) if op=='cont' else (0,0)
    a,b=bounds(r[1]),bounds(r[2])
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)

@lru_cache(None)
def normal(i):
    r=ast[i]
    if r[0]=='L':return tuple([dict(dec='D',inc='I',brk='B',cont='C',halt='H')[r[1][0]]]+r[1][1:])
    a,b=r[1:]; aa,bb=normal(a),normal(b)
    if bounds(a)==bounds(b)==(0,0):
        return ('S',*(aa[1:]if aa[0]=='S'else(aa,)),*(bb[1:]if bb[0]=='S'else(bb,)))
    return ('A',aa,bb)

normatom={normal(v):k for k,v in cm['fine_ast_ids'].items()}
assert len(normatom)==30
macro={k:''.join(normatom[t]for t in w)for k,w in sm.MACROS.items()}
def emit(row):return ''.join(macro[k]for k in sm.emit(row))
def rename(t,m):
    if isinstance(t,str):return m.get(t,t)
    if isinstance(t,tuple):return tuple(rename(x,m)for x in t)
    return t
maps=[dict(zip(('a','b','c'),p))for p in itertools.permutations(('a','b','c'))]
variants=[[emit(rename(row,m))for m in maps]for row in sm.ROWS[1:]]
rows=[v[0]for v in variants]
prefix=''.join(macro[k]for k in [166,121,180,176])
pre=prefix+''.join(rows)
assert ax.startswith(pre)
tail=ax[len(pre):]
ls=(REF/'inputs/canonical-grammar.txt').read_text().splitlines()
n,nr,na=map(int,ls[0].split())
terms={w:int(m)for w,m in map(str.split,ls[n+1+nr:])}
roots=(set(base['roots'])|{r['word']for r in base['routes']})-{ax}
@lru_cache(None)
def closure(w):
    if w in terms:return frozenset()
    return frozenset({w})|closure(g[w][0])|closure(g[w][1])
core=frozenset().union(*(closure(w)for w in roots))
private=sorted(set(g)-core)
assert len(private)<=128
pindex={w:i for i,w in enumerate(private)}
tokens=sorted(set(g)|set(terms))
out=[f'{len(tokens)} {len(core)} {len(private)}']
for w in tokens:
    mask=sum(1<<pindex[t]for t in closure(w)-core)
    out.append(f'{w} {mask&((1<<64)-1)} {mask>>64} {terms.get(w,3)}')
out.append(prefix);out.append(tail);out.append('8')
for vv in variants:out.extend(vv)
(HERE/'axiom_search.txt').write_text('\n'.join(out)+'\n')
(HERE/'axiom_search_metadata.json').write_text(json.dumps(dict(base=base,core=sorted(core),private=private,terms=terms,tokens=tokens,prefix=prefix,tail=tail,variants=variants,maps=maps,reference='vendor'),indent=2)+'\n')
print(json.dumps(dict(tokens=len(tokens),core=len(core),private=len(private),prefix=len(prefix),tail=len(tail),rows=list(map(len,rows)))))
