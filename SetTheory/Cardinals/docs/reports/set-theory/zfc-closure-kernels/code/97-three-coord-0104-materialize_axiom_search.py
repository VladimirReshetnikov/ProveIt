#!/usr/bin/env python3
"""Construct actual shared grammars for AX-symmetry dictionary parses.

The output is an abstract source grammar, not a certified Turing machine.
All non-AX roots, existing productions, routes, and bootstrap locks are kept.
New words are joined using orientation-safe binary trees and exact dependency
sets. Identical new words receive the same chosen production.
"""
import sys,json,argparse
from pathlib import Path
from functools import lru_cache

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--metadata',type=Path,default=HERE/'axiom_search_metadata.json')
parser.add_argument('files',nargs='*',type=Path)
args=parser.parse_args()
m=json.loads(args.metadata.read_text())
base=m['base'];g={w:(a,b)for w,a,b in base['rules']};terms=m['terms'];core=set(m['core'])
ax=max(base['roots'],key=len)
REF=Path(m['reference'])
if not REF.is_absolute():REF=HERE/REF
source=json.loads((REF/'reference_data/reference/grammar/closed-sequence-grammar-next22.json').read_text())
symbols=json.loads((REF/'reference_data/reference/grammar/semantic-symbols.json').read_text())
cm=json.loads((REF/'inputs/canonical-map.json').read_text())
ast=source['ast_dag'];enc=cm['physical_atoms']
canonical=lambda w:''.join(enc[c]for c in w)
lines=(REF/'reference_data/reference/grammar/semantic.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split())
names={int(q):canonical(w)for k,w,q in map(str.split,lines[1:n+1])}
old={canonical(w):(canonical(w[:int(k)]),canonical(w[int(k):]))for k,w,q in map(str.split,lines[1:n+1])}
by_ast={int(a):names[int(q)]for q,a in source['sequence_ast_roots'].items()}
terminal_ast={enc[c]:source['atoms'][name]['ast']for c,name in symbols.items()}

def join_prop(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1
@lru_cache(None)
def wp(w):
    return ep(terminal_ast[w])if w in terminal_ast else join_prop(*(wp(x)for x in g.get(w,old.get(w))))
@lru_cache(None)
def ep(i):
    if i in by_ast:return wp(by_ast[i])
    r=ast[i]
    return (0,0,0)if r[0]=='L'else join_prop(ep(r[1]),ep(r[2]))
@lru_cache(None)
def deps(w):
    if w in terms:return frozenset()
    return frozenset({w})|deps(g[w][0])|deps(g[w][1])

def materialize(rec):
    parts=rec['parts'];ng=dict(g)
    prefix=['']
    for t in parts:prefix.append(prefix[-1]+t)
    @lru_cache(None)
    def parse(w,seq):
        if w in terms:return (frozenset(),wp(w),None)
        if w in g:return (deps(w)-core,wp(w),None)
        best=None
        for k in range(1,len(seq)):
            a=''.join(seq[:k]);b=''.join(seq[k:])
            if a in terms and not terms[a]&1:continue
            if b in terms and not terms[b]&2:continue
            left=parse(a,seq[:k]);right=parse(b,seq[k:])
            if left is None or right is None:continue
            prop=join_prop(left[1],right[1])
            if prop[1]>6 or prop[2]>64:continue
            nodes=left[0]|right[0]|{w}
            candidate=(nodes,prop,(a,b))
            score=(len(nodes),prop[0],prop[2])
            if best is None or score<(len(best[0]),best[1][0],best[1][2]):best=candidate
        return best
    result=parse(prefix[-1],tuple(parts))
    if result is None:return None
    # Every new interval is memoized by its actual substring and identical
    # token decomposition. Conflicting shared productions are rejected.
    chosen={}
    def realize(w,seq):
        r=parse(w,seq)
        if r[2]is None:return
        a,b=r[2]
        if w in chosen:assert chosen[w]==(a,b)
        chosen[w]=(a,b);ng[w]=(a,b)
        k=next(i for i in range(1,len(seq))if ''.join(seq[:i])==a)
        realize(a,seq[:k]);realize(b,seq[k:])
    realize(prefix[-1],tuple(parts))
    live=set()
    def visit(w):
        if w in terms or w in live:return
        live.add(w)
        for child in ng[w]:visit(child)
    roots=[prefix[-1]if x==ax else x for x in base['roots']]
    for w in roots+[r['word']for r in base['routes']]:visit(w)
    d=dict(base,status='AX_SYMMETRY_ABSTRACT_GRAMMAR',rules_count=len(live),
        rules=[[w,*ng[w]]for w in sorted(live)],roots=roots,
        source_replacements={ax:prefix[-1]},axiom_order=rec['order'],axiom_roles=rec['roles'],
        role_maps=m['maps'],dictionary_trial=rec['trial'],AX_properties=result[1])
    if 'source_override'in base:
        d['source_override']=dict(base['source_override'],new_word=prefix[-1])
        d['source_replacements']={base['source_override']['original_word']:prefix[-1]}
    if 'basis'in m:
        d['status']='AX_BASIS_ABSTRACT_GRAMMAR'
        d['basis']=m['basis']
    assert len(live)<=rec['cost_upper_bound']
    return d

def main():
    incoming=args.files or [args.metadata.parent/'enumerate.jsonl']
    outdir=args.metadata.parent/'candidates';outdir.mkdir(exist_ok=True)
    seen=set();best=10000;counts={};valid=0
    for fn in incoming:
        for line in fn.read_text().splitlines():
            rec=json.loads(line);sig=tuple(rec['order'])+tuple(rec['roles'])
            if sig in seen:continue
            seen.add(sig)
            d=materialize(rec)
            if d is None:continue
            valid+=1;n=d['rules_count'];counts[n]=counts.get(n,0)+1
            if n<=128 or ('basis'in m and n<=135 and n<best):
                path=outdir/f'axiom-{n}-{fn.stem}-{rec["trial"]}.json'
                path.write_text(json.dumps(d,indent=2)+'\n')
            if n<best:best=n;print('BEST',n,fn.stem,rec['trial'],d['AX_properties'],flush=True)
    summary=dict(status='BOUNDED_ABSTRACT_SOURCE_SEARCH',unique_proposals=len(seen),valid=valid,best_grammar=best,counts=counts)
    (args.metadata.parent/'materialization_results.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)
if __name__=='__main__':main()
