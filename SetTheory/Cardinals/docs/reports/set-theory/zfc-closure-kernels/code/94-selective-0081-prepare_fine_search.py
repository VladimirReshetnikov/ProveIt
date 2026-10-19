"""Normalize grammar words by exact equality of finest closed AST atoms.

No instruction commutation or theory change occurs. The 44 opaque terminals
remain available as zero-extra-cost alternatives for their exact words in
the 30-atom alphabet.
"""
import json
from functools import cache
from pathlib import Path
from grammar_model import BASE, load

HERE=Path(__file__).resolve().parent
s=json.loads((BASE/'inputs/closed-sequence-grammar-next22.json').read_text())
symbols=json.loads((BASE/'inputs/semantic-symbols.json').read_text())
ast=s['ast_dag']
@cache
def bounds(i):
    r=ast[i]
    if r[0]=='L':
        op,*a=r[1]
        return (1,0) if op=='dec' else (a[0],0) if op=='brk' else (0,a[0]) if op=='cont' else (0,0)
    a,b=bounds(r[1]),bounds(r[2])
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
@cache
def finest(i):
    r=ast[i]
    return finest(r[1])+finest(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
atomids={c:finest(s['atoms'][n]['ast']) for c,n in symbols.items()}
single={ids[0]:c for c,ids in atomids.items() if len(ids)==1}
expansions={c:''.join(single[i] for i in ids) for c,ids in atomids.items()}
assert len(single)==30 and len(set(expansions.values()))==44
def norm(w): return ''.join(expansions[c] for c in w)

def main():
    data,g,old,roots,allowed,groups,exprs,orig,atoms,locks=load()
    assert len({norm(w) for w in old})==len(old)
    assert not set(map(norm,old)) & set(expansions.values())
    lines=(BASE/'inputs/state_reduction/route-grammar.txt').read_text().splitlines()
    nr,nroot,na=map(int,lines[0].split())
    new=[lines[0]]
    for k,w,q in map(str.split,lines[1:nr+1]):
        new.append(f'{len(norm(w[:int(k)]))} {norm(w)} {q}')
    new.extend(norm(w) for w in lines[nr+1:nr+1+nroot])
    new.extend(f'{expansions[c]} {mask}' for c,mask in allowed.items())
    (HERE/'fine-grammar.txt').write_text('\n'.join(new)+'\n')
    out=[str(len(groups))]
    for q,b,w,cs in groups:
        out.append(f'{q} {b} {norm(w)} {len(cs)}')
        out.extend(f'{p} {norm(t)}' for p,t in cs)
    out.append(f'{len(exprs)} {orig} {len(atoms)}')
    for e in exprs:
        out.append('W '+norm(e[1]) if e[0]=='W' else ' '.join(e))
    out.extend(f'{expansions[c]} {a}' for c,a in atoms.items())
    (HERE/'fine-constraints.txt').write_text('\n'.join(out)+'\n')
    out=[str(sum(len(x) for x in locks.values()))]
    out.extend(f'{norm(w)} {b} {norm(t)}' for w,ts in locks.items() for b,t in enumerate(ts))
    (HERE/'fine-boot54.txt').write_text('\n'.join(out)+'\n')
    out=[str(len(g))]+[f'{len(norm(a))} {norm(w)}' for w,(a,b) in g.items()]
    out.append(str(len(data['routes'])))
    out.extend(norm(r['word']) for r in data['routes'])
    (HERE/'fine-current128.resume').write_text('\n'.join(out)+'\n')
    (HERE/'fine-atom-identities.json').write_text(json.dumps(dict(expansions=expansions,ast_ids=atomids),indent=2)+'\n')
    src=(BASE/'code/state_reduction/anneal_routes_zero6.cpp').read_text()
    src=src.replace('unordered_map<char,int> atomExpr','unordered_map<int,int> atomExpr')
    src=src.replace('unordered_map<char,int> allowed','unordered_map<int,int> allowed')
    src=src.replace('return words[q].size()==1;', 'return allowed.count(q);')
    src=src.replace('allowed[words[a][0]]','allowed[a]').replace('allowed[words[b][0]]','allowed[b]')
    src=src.replace('atomExpr.at(words[q][0])','atomExpr.at(q)')
    src=src.replace('active.push_back(intern(string(1,c)))','active.push_back(c)')
    src=src.replace('char c;int m;f>>c>>m;allowed[c]=m;', 'string c;int m;f>>c>>m;allowed[intern(c)]=m;')
    src=src.replace('char c;int a;cf>>c>>a;atomExpr[c]=a;', 'string c;int a;cf>>c>>a;atomExpr[intern(c)]=a;')
    src=src.replace('ABSTRACT_ROUTING_GRAMMAR_ONLY','FINE_ATOM_ROUTING_GRAMMAR_ONLY')
    src=src.replace('// Routing-aware extension of ProveIt incoming anneal5.cpp; see NOTICE.txt.', '// Fine-atom extension of the attributed routed245 annealer.\n// See fine-atom-identities.json; exact AST identities, no commutations.')
    (HERE/'anneal_fine.cpp').write_text(src)
    print(json.dumps({'fine_atoms':len(single),'opaque_atom_alternatives':len(expansions),'initial_rules':len(g),'largest_root_fine_length':max(map(lambda w:len(norm(w)),roots))},indent=2))

if __name__=='__main__':main()
