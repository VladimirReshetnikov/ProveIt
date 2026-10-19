#!/usr/bin/env python3
"""Finite source/grammar checks only; machine certification is separate."""
from __future__ import annotations
import argparse, hashlib, json
from functools import lru_cache
from pathlib import Path
ROOT = Path(__file__).resolve().parent

def read(path): return json.loads(Path(path).read_text())

def check(candidate, reference=ROOT/'reference_data', required_locks=0):
    reference=Path(reference)
    source=read(reference/'reference/grammar/closed-sequence-grammar-next22.json')
    symbols=read(reference/'reference/grammar/semantic-symbols.json'); ast=source['ast_dag']
    @lru_cache(None)
    def bounds(i):
        r=ast[i]
        if r[0]=='L':
            op,*arg=r[1]
            return (1,0) if op=='dec' else (arg[0],0) if op=='brk' else (0,arg[0]) if op=='cont' else (0,0)
        a,b=bounds(r[1]),bounds(r[2])
        return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
    @lru_cache(None)
    def finest(i):
        r=ast[i]
        return finest(r[1])+finest(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
    fine={c:finest(source['atoms'][name]['ast'])for c,name in symbols.items()}
    alphabet=sorted({i for values in fine.values()for i in values})
    assert len(alphabet)==30 and all(bounds(i)==(0,0)for i in alphabet)
    codes={i:'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'[j]for j,i in enumerate(alphabet)}
    encoding={c:''.join(codes[i]for i in values)for c,values in fine.items()}
    assert len(encoding)==len(set(encoding.values()))==44
    def canonical(w):return ''.join(encoding[c]for c in w)
    def raw_grammar(path):
        lines=path.read_text().splitlines();n,nr,na=map(int,lines[0].split())
        rows=[row.split()for row in lines[1:n+1]]
        names={int(q):canonical(w)for k,w,q in rows}
        rules={canonical(w):(canonical(w[:int(k)]),canonical(w[int(k):]))for k,w,q in rows}
        roots=[canonical(w)for w in lines[n+1:n+1+nr]]
        masks={encoding[c]:int(m)for c,m in map(str.split,lines[n+1+nr:])}
        assert len(masks)==na
        return names,rules,roots,masks
    names,old,_,masks=raw_grammar(reference/'reference/grammar/semantic.txt')
    _,_,source_roots,search_masks=raw_grammar(reference/'inputs/state_reduction/route-grammar.txt')
    assert masks==search_masks
    terminal={encoding[c]:source['atoms'][name]['ast']for c,name in symbols.items()}
    by_ast={int(a):names[int(q)]for q,a in source['sequence_ast_roots'].items()}
    d=read(candidate);assert not d.get('source_replacements'),'Unchanged source word required.'
    rules={w:(a,b)for w,a,b in d['rules']}
    assert len(rules)==len(d['rules'])==d['rules_count']
    assert set(source_roots)<=set(d['roots'])
    for w,(a,b)in rules.items():
        assert w not in terminal and a and b and w==a+b and set(w)<=set(codes.values())
        assert (a in rules or a in terminal)and(b in rules or b in terminal)
        assert a not in terminal or masks[a]&1
        assert b not in terminal or masks[b]&2
    def project(w,prefix):
        for bit in prefix:
            assert w in rules,(w,prefix)
            w=rules[w][int(bit)]
        return w
    routes={(r['source'],r['read']):r['word']for r in d['routes']}
    assert len(routes)==len(d['routes'])
    lines=(reference/'inputs/state_reduction/route-constraints.txt').read_text().splitlines()
    ng,p,projections=int(lines[0]),1,0
    assert ng==len(routes)==11
    for _ in range(ng):
        src,bit,original,nc=lines[p].split();p+=1;word=routes[int(src),int(bit)]
        for _ in range(int(nc)):
            prefix,target=lines[p].split();p+=1
            assert project(word,prefix)==canonical(target)
            projections+=1
    assert projections==22
    lines=(reference/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()
    locks=[(canonical(w),bit,canonical(t))for w,bit,t in map(str.split,lines[1:])]
    changed=[dict(word=w,bit=int(bit),target=t)for w,bit,t in locks if w not in rules or rules[w][int(bit)]!=t]
    if required_locks==54:assert not changed
    elif required_locks==50:
        obsolete={canonical('eijkKCqkjGeU'),canonical('eijkKCqkjGe')}
        assert all(item['word']in obsolete for item in changed)and len(changed)<=4
    reachable=set()
    def visit(w):
        if w in terminal or w in reachable:return
        assert w in rules;reachable.add(w)
        for child in rules[w]:visit(child)
    for word in d['roots']+list(routes.values()):visit(word)
    assert reachable==set(rules),'Unreachable rules distort the state count.'
    visiting=set()
    def combine(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1,a[3]+b[3]
    @lru_cache(None)
    def wp(w):
        assert w not in visiting,'Semantic atom/source cycle.'
        visiting.add(w)
        value=ep(terminal[w])if w in terminal else combine(*(wp(x)for x in rules.get(w,old.get(w))))
        visiting.remove(w);return value
    @lru_cache(None)
    def ep(i):
        if i in by_ast:return wp(by_ast[i])
        r=ast[i]
        return (0,0,0,(tuple(r[1]),))if r[0]=='L'else combine(ep(r[1]),ep(r[2]))
    @lru_cache(None)
    def leaves(i):
        r=ast[i]
        return (tuple(r[1]),)if r[0]=='L'else leaves(r[1])+leaves(r[2])
    lead,zero,depth,word=ep(source['original_ast'])
    assert word==leaves(source['original_ast'])and len(word)==6460
    return dict(status='PASS_ABSTRACT_CANONICAL_GRAMMAR',candidate=Path(candidate).name,
                sha256=hashlib.sha256(Path(candidate).read_bytes()).hexdigest(),grammar_rules=len(rules),
                dictionary_terminals=44,finest_closed_atoms=30,route_projections=projections,
                original_locks_preserved=54-len(changed),changed_locks=changed,
                source_leading_zero_depth=lead,source_maximum_zero_run=zero,source_binary_depth=depth,
                exact_ordered_instruction_leaves=len(word),
                scope='Finite source/grammar check only; literal table, affine runtime, padding, and blank bootstrap require independent certification.')

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must be enabled.')
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('candidate',type=Path)
    p.add_argument('--reference',type=Path,default=ROOT/'reference_data')
    p.add_argument('--locks',type=int,choices=(0,50,54),default=0);p.add_argument('--output',type=Path)
    a=p.parse_args();result=check(a.candidate,a.reference,a.locks);text=json.dumps(result,indent=2)+'\n'
    print(text,end='')
    if a.output:a.output.write_text(text)
