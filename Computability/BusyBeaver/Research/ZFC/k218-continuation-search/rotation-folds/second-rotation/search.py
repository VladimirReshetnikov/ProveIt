"""Bounded second-rotation literal duplicate-row census, not general fold search."""
from pathlib import Path
from collections import Counter, defaultdict
import argparse
import hashlib
import itertools
import json
import os
import sys
import time

sys.dont_write_bytecode = True
ap = argparse.ArgumentParser()
ap.add_argument('--repo', type=Path, required=True)
ap.add_argument('--inputs', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
ap.add_argument('--seconds', type=int, default=120)
a = ap.parse_args()
assert __debug__ and not os.environ.get('PYTHONOPTIMIZE')
assert 1 <= a.seconds <= 120
a.output.mkdir(parents=True, exist_ok=False)
library = a.repo / 'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {str(library/name): sha(library/name) for name in ['source_language.py','build221.py']}
sys.path.insert(0, str(library))
import source_language as s
import build221 as b

def replace(t, old, new):
    if t == old:return new
    if s.leaf(t):return t
    return tuple(replace(child, old, new) for child in t)

def duplicates(table):
    byrows = defaultdict(list)
    for q in sorted({q for q,bit in table}):
        byrows[table[q,0],table[q,1]].append(q)
    return [list(pair) for group in byrows.values() for pair in itertools.combinations(group,2)]

begun = time.monotonic();total = Counter();parents=[];hits=[];complete=True
for seed in ['primary','contextual']:
    census_path = a.inputs/seed/'census.json';pins[str(census_path)] = sha(census_path)
    census = json.loads(census_path.read_text())
    for first in census['rotations']:
        if time.monotonic()-begun >= a.seconds:complete=False;break
        folder = a.inputs/seed/first['name']
        for name in ['native.tm','sites.json']:pins[str(folder/name)] = sha(folder/name)
        table = b.read_table((folder/'native.tm').read_bytes())
        src = json.loads((folder/'sites.json').read_text());tree = s.tree(src)
        groups,paths = b.decoder_map(table,tree)
        incoming=defaultdict(set)
        for key,act in table.items():incoming[act[2]].add(key)
        olddups = duplicates(table);assert not olddups, ('parent already has exact duplicates',seed,first['name'],olddups)
        stats=Counter();stopped=False
        for q,ns in sorted(groups.items()):
            if len(ns)!=1:continue
            node=next(iter(ns))
            for edge in (0,1):
                if time.monotonic()-begun >= a.seconds:complete=False;stopped=True;break
                r=table[q,edge][2]
                if s.leaf(node[edge]) or groups.get(r,set())!={node[edge]}:continue
                if q==r or incoming[r]!={(q,edge)}:continue
                if not all(table[z,bit][:2]==(bit,1)for z in (q,r)for bit in(0,1)):continue
                stats['pure_unique']+=1
                if edge==0:
                    (A,B),C=node;newnode=A,(B,C)
                    actions={(q,0):(0,1,table[r,0][2]),(q,1):(1,1,r),
                             (r,0):(0,1,table[r,1][2]),(r,1):(1,1,table[q,1][2])}
                else:
                    A,(B,C)=node;newnode=(A,B),C
                    actions={(q,0):(0,1,r),(q,1):(1,1,table[r,1][2]),
                             (r,0):(0,1,table[q,0][2]),(r,1):(1,1,table[r,0][2])}
                if not all(s.boundary(x)==(0,0,False)for x in (A,B,C)):continue
                stats['closed']+=1
                newtable=table|actions;dups=duplicates(newtable)
                # Do not run new CFG/prefix validation unless a literal duplicate exists.
                if not dups:stats['no_literal_duplicate']+=1;continue
                stats['literal_duplicate_layouts']+=1
                newtree=replace(tree,node,newnode);rows=s.sites(newtree)
                if rows[:37]!=src[:37]:stats['initial37_changed']+=1;continue
                metrics=s.metrics(newtree)
                if metrics['maximum_zero_run']>6:stats['zero_run_too_long']+=1;continue
                assert [x[1:]for x in rows]==[x[1:]for x in src]
                assert s.graph_arithmetic(rows)[0]==s.graph_arithmetic(src)[0]==s.graph_intervals(rows)
                try:actual,_=b.decoder_map(newtable,newtree)
                except (ValueError,KeyError):stats['decoder_failed']+=1;continue
                expected={z:{replace(n,node,newnode)for n in old}for z,old in groups.items()}
                expected[r]={newnode[1-edge]}
                if dict(actual)!=expected:stats['binding_failed']+=1;continue
                stats['source_binding_duplicate_hits']+=1
                name=f'{seed}-{first["name"]}--q{q}-r{r}-edge{edge}'
                out=a.output/name;out.mkdir()
                (out/'parent218.tm').write_bytes(b.table_bytes(newtable))
                (out/'sites.json').write_bytes(s.compact(rows))
                entry={'seed':seed,'first':first['name'],'second':{'q':q,'r':r,'edge':edge},
                       'duplicates':dups,'metrics':metrics,'folder':name,
                       'scope':'Two-rotation source/CFG/internal-prefix check only; parent runtime/startup unproved.'}
                for keep,drop in dups:
                    phi=lambda z:keep if z==drop else z
                    folded={(z,bit):(w,d,phi(t))for(z,bit),(w,d,t)in newtable.items()if z!=drop}
                    assert len(folded)==434
                    assert all(folded[phi(z),bit]==(w,d,phi(t))for(z,bit),(w,d,t)in newtable.items())
                    (out/f'fold-{keep}-{drop}-217.tm').write_bytes(b.table_bytes(folded,phi(0)))
                hits.append(entry)
                print('LITERAL_DUPLICATE_HIT',json.dumps(entry),flush=True)
            if stopped:break
        total.update(stats)
        parents.append({'seed':seed,'first':first['name'],'status':'PARTIAL'if stopped else'COMPLETE','counts':dict(stats)})
        print('PARENT',seed,first['name'],dict(stats),flush=True)
        if not complete:break
    if not complete:break
result={'status':'SECOND_ROTATION_FAMILY_COMPLETE'if complete else'SOFT_DEADLINE',
        'seconds':time.monotonic()-begun,'limit_seconds':a.seconds,'counts':dict(total),
        'parents':parents,'hits':hits,'input_pins':pins,'source_sha256':sha(Path(__file__)),
        'scope':'Exactly one further pure unique-child closed rotation from each frozen first parent. Literal two-row duplicates only; no common-branch synthesis or general fold search. New CFG/internal-prefix checks run only for duplicates passing unchanged-first37 and zero-run<=6. Parent runtime and startup remain unproved even for a hit.'}
(a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('parents','input_pins')}),flush=True)
