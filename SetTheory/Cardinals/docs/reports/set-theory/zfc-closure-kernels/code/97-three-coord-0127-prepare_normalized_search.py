#!/usr/bin/env python3
"""Compose the earlier verified DNE normalization with AX row symmetries."""
import json
from pathlib import Path
from functools import lru_cache
HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'axiom_search_metadata.json').read_text())
path=HERE/'vendor/normalized_grammar.json'
base=json.loads(path.read_text());g={w:(a,b)for w,a,b in base['rules']}
terms=m['terms'];ax=max(base['roots'],key=len)
pre=m['prefix']+''.join(v[0]for v in m['variants'])
assert ax.startswith(pre)
roots=(set(base['roots'])|{r['word']for r in base['routes']})-{ax}
@lru_cache(None)
def closure(w):
    if w in terms:return frozenset()
    return frozenset({w})|closure(g[w][0])|closure(g[w][1])
core=frozenset().union(*(closure(w)for w in roots));private=sorted(set(g)-core)
assert len(private)<=128
pindex={w:i for i,w in enumerate(private)};tokens=sorted(set(g)|set(terms))
lines=[f'{len(tokens)} {len(core)} {len(private)}']
for w in tokens:
    mask=sum(1<<pindex[t]for t in closure(w)-core)
    lines.append(f'{w} {mask&((1<<64)-1)} {mask>>64} {terms.get(w,3)}')
tail=ax[len(pre):]
lines += [m['prefix'],tail,'8']+[w for row in m['variants']for w in row]
out=HERE/'normalized';out.mkdir(exist_ok=True)
(out/'input.txt').write_text('\n'.join(lines)+'\n')
m.update(base=base,core=sorted(core),private=private,tokens=tokens,tail=tail,
    source_normalization='DNE mask32 from the earlier fully audited normalized245 machine',
    normalized_reference='vendor/normalized_grammar.json')
(out/'metadata.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps(dict(tokens=len(tokens),core=len(core),private=len(private),ax_length=len(ax),tail_length=len(tail))))
