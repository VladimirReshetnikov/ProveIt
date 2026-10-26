#!/usr/bin/env python3
"""Read-only source161 discriminant redundancy check against the delivered package."""
from pathlib import Path
from hashlib import sha256
import argparse
import json

def require(value, message):
    if not value:
        raise ValueError(message)

def read(path):
    return json.loads(path.read_text())

def poly(row):
    return {tuple(m):c for c,m in row['terms']}

def main(root):
    parentpath = root/'composition/157-linear-crt/source/equation.json'
    parent = read(parentpath)
    names = {v['name']:i for i,v in enumerate(parent['variables'])}
    a, d = names['shared.A'], names['index_addition.D']
    require(d == 170, 'parent D coordinate')
    uses = [j for j,r in enumerate(parent['residuals']) if any(d in m for c,m in r['terms'])]
    require(uses == [123,124], 'complete D occurrence list')
    require(poly(parent['residuals'][123]) == {(d,):1,(a,a):-1,(a,):-2}, 'literal D definition')
    cert = read(root/'composition/composed/strict238/strict_certificate.json')
    require(cert['parent_sha256'] == sha256(parentpath.read_bytes()).hexdigest(), 'parent source hash')
    require(cert['removed_variables'] == [112,170,171,233], 'strict removed coordinates')
    require(cert['removed_names'] == ['pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1'], 'strict removed names')
    require(cert['removed_rows'] == [123,124,173], 'strict removed rows')
    keep = [i for i,j in cert['old_to_new']]
    require(d not in keep and set(keep) == set(range(242))-{112,170,171,233}, 'coordinate retention excludes D')
    absent = []
    for stage in ('strict238','basis235','pooled223','differences223'):
        path = root/f'composition/composed/{stage}/equation.json'
        equation = read(path)
        require(all(v['name'] != 'index_addition.D' for v in equation['variables']), f'D absent in {stage}')
        absent.append(stage)
    norm_rows = {}
    for name, equation in [('parent242',parent), ('Balanced218',read(root/'algebra/equation218.json')), ('Centered216',read(root/'algebra/equation216.json'))]:
        ids = {v['name']:i for i,v in enumerate(equation['variables'])}
        require('index_addition.D' not in ids or name == 'parent242', f'D absent in {name}')
        a,u,v = [ids[k] for k in ('shared.A','mul.450','mul.451')]
        want = {(a,a):1,(a,):2,(u,u):1,(v,v):-1}
        matches = [(j,r) for j,r in enumerate(equation['residuals']) if r['label']=='shared.last_norm']
        require(len(matches)==1 and poly(matches[0][1])==want, f'explicit discriminant in {name} last norm')
        norm_rows[name]=matches[0][0]
    require(norm_rows=={'parent242':105,'Balanced218':96,'Centered216':94}, 'last norm row indices')
    return dict(status='passed', parent_sha256=sha256(parentpath.read_bytes()).hexdigest(),
                discriminant_coordinate=d, discriminant_uses=uses,
                strict_removed_coordinates=cert['removed_variables'],
                strict_removed_rows=cert['removed_rows'], subsequent_absence=absent,
                final_absence=['Balanced218','Centered216'], last_norm_rows=norm_rows,
                conclusion='Source161 discriminant contraction is already subsumed by the strict-horizon stage; no additional variable reduction.')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('package', type=Path)
    args=ap.parse_args()
    print(json.dumps(main(args.package), indent=2))
