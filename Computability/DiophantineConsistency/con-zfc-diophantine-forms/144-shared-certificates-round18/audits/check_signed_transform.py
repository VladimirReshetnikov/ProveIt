#!/usr/bin/env python3
"""Independent named-coordinate reconstruction; does not import producer code."""
import copy
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'prior_direct_closure/direct'
GROUPS = [
    ('pow4.output', (3,12), ('choose0.remainder','range8.remainder')),
    ('pow6.output', (4,5,6,7,13), ('range0.remainder','range1.remainder','range2.remainder','range3.remainder','range9.remainder')),
    ('pow11.output', (8,9), ('range4.remainder','range5.remainder')),
    ('pow14.output', (10,11), ('range6.remainder','range7.remainder')),
]

def require(x, msg):
    if not x:
        raise ValueError(msg)

def plus(*parts):
    out = defaultdict(int)
    for p in parts:
        for m,c in p.items():
            out[m] += c
    return {m:c for m,c in out.items() if c}

def times(p,q):
    out = defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():
            out[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in out.items() if c}

def scaled(p,a):
    return {m:c*a for m,c in p.items() if c*a}

def v(name):
    return {(name,):1}

def row_named(row,names):
    out = defaultdict(int)
    for c,mon in row['terms']:
        out[tuple(sorted(names[i] for i in mon))] += c
    return {m:c for m,c in out.items() if c}

def fingerprint(row):
    return tuple(sorted(row.items()))

def checked(path, supplied=None):
    cert=json.loads((path/'certificate.json').read_text())
    old=json.loads((path/'source_equation.json').read_text())
    prior=json.loads((BASE/cert['source_endpoint']/'equation.json').read_text())
    require(old==prior, 'baseline equation differs from retained round17')
    tr=json.loads((path/'source_translation.json').read_text())
    require(tr==json.loads((BASE/cert['source_endpoint']/'translation_certificate.json').read_text()), 'translation binding')
    names=[z['name'] for z in old['variables']]
    require(len(set(names))==len(names),'duplicate baseline names')
    shifts={names[i]:s for i,s in tr['shifts']}
    def a(name): return plus(v(name),{():shifts.get(name,0)})
    def ternary(g):
        aa,bb,cc=(v(f'guard{g}.{x}') for x in ('a','b','c'))
        return plus(times(aa,aa),times(bb,bb),times(cc,cc),cc)
    oldrows={r['label']:row_named(r,names) for r in old['residuals'] if r['label'].startswith('domain_guard.')}
    removed=set()
    for denom,guards,remainders in GROUPS:
        for g,r in zip(guards,remainders):
            expected=plus(times(a(r),a(denom)),scaled(a(r),-1),scaled(times(a(r),a(r)),-1),scaled(ternary(g),-1))
            label=f'domain_guard.{g}'
            require(oldrows[label]==expected,('incorrect original interval guard',label))
            removed.add(label)
    if cert['odd_square_radix']:
        require(oldrows['domain_guard.2']==plus(a('pow2.output'),scaled(a('choose0.output'),-1),{():-1},scaled(ternary(2),-1)),'old q output guard shape')
        removed.add('domain_guard.2')
    expected=[(r['label'],row_named(r,names)) for r in old['residuals'] if r['label'] not in removed]
    groups=[(d,g,[(r,a(r)) for r in rs]) for d,g,rs in GROUPS]
    if cert['merged']:
        first=[]
        for r in GROUPS[0][2]:
            new='sphere.scaled.'+r
            expected.append(('sphere.scale.'+r,plus(v(new),scaled(times(a('pow2.output'),a(r)),-1))))
            first.append((r,v(new)))
        groups=[(GROUPS[1][0],GROUPS[0][1]+GROUPS[1][1],first+groups[1][2])]+groups[2:]
    for i,(denom,guards,rs) in enumerate(groups):
        expected.append(('sphere.interval_group.'+str(i),plus(times(a(denom),a(denom)),*(scaled(times(p,p),-2) for _,p in rs),scaled(ternary(guards[0]),-1))))
    if cert['odd_square_radix']:
        root=plus(scaled(v('radix.odd_square_root'),2),{():1})
        expected.append(('radix.odd_square',plus(a('pow2.output'),scaled(times(root,root),-1))))
    new=supplied or json.loads((path/'equation.json').read_text())
    nn=[z['name'] for z in new['variables']]
    require(len(set(nn))==len(nn),'duplicate output names')
    got=Counter((r['label'],fingerprint(row_named(r,nn))) for r in new['residuals'])
    want=Counter((label,fingerprint(p)) for label,p in expected)
    require(got==want,'complete named residual multiset differs from independent reconstruction')
    used={name for _,p in expected for mon in p for name in mon}
    require(set(nn)==used,'unused, missing, or unexplained variables')
    require(all(len(mon)<=2 for _,p in expected for mon in p),'nonquadratic row')
    return {'endpoint':path.name,'variables':len(nn),'rows':len(new['residuals']),
            'groups':[len(rs) for _,_,rs in groups],'odd_square':cert['odd_square_radix'],
            'equation_sha256':hashlib.sha256((path/'equation.json').read_bytes()).hexdigest()}

def main():
    records=[]
    controls=0
    for path in sorted((ROOT/'signed').glob('sphere_*')):
        if not (path/'certificate.json').exists():continue
        records.append(checked(path))
        original=json.loads((path/'equation.json').read_text())
        for row in original['residuals']:
            if not row['label'].startswith(('sphere.','radix.odd_square')): continue
            bad=copy.deepcopy(original)
            changed=next(r for r in bad['residuals'] if r['label']==row['label'])
            changed['terms'][0][0]+=1
            try: checked(path,bad)
            except ValueError: controls+=1
            else: raise ValueError(('mutation accepted',path.name,row['label']))
    receipt={'status':'PASS','scope':'exact complete named-coordinate transformation, including old guard recognition, unchanged rows, affine shifts, merging, odd square, variable support, quadraticity','endpoints':records,'mutated_new_rows_rejected':controls}
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
