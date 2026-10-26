#!/usr/bin/env python3
"""Authenticate package166's literal 21-atom frame and canonical parity.

Input: the unmodified stages/compressed/raw_source.json from pinned package166.
This proves finite polynomial identities; the availability of canonical
semantic witnesses is the separately cited completeness construction.
"""
import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


def add(*polys):
    out=defaultdict(int)
    for p in polys:
        for m,c in p.items():
            out[m]+=c
    return {m:c for m,c in out.items() if c}


def mul(p,q):
    out=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():
            out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}


def v(i):
    return {(i,):1}


def c(n):
    return {():n} if n else {}


def mod2(p):
    out=set()
    for m,a in p.items():
        if a%2:
            m=tuple(sorted(set(m)))
            if m in out:
                out.remove(m)
            else:
                out.add(m)
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('source',type=Path)
    args=ap.parse_args()
    data=args.source.read_bytes()
    raw=json.loads(data)
    names={z['name']:i for i,z in enumerate(raw['variables'])}
    if names['shared.W']!=245 or names['add.380']!=171:
        raise ValueError('different source coordinate boundary')
    row=next(r for r in raw['residuals'] if r['label']=='shared.frame_definition')
    old={tuple(m):a for a,m in row['terms']}
    atoms=[add(v(0),c(16)),v(1),add(v(2),c(1)),add(v(4),v(0),c(16)),v(5)]
    atoms.extend(add(v(i),c(1)) for i in range(16,25))
    atoms.extend([v(26),add(v(171),c(1)),v(179),v(181),v(211),v(223),v(522)])
    if len(atoms)!=21:
        raise ValueError('wrong atom count')
    sigma=add(*(mul(a,a) for a in atoms))
    rebuilt=add(v(245),c(-2),{m:-a for m,a in sigma.items()})
    if old!=rebuilt:
        raise ValueError('literal frame does not match the complete atom list')
    # Exact GF(2) propagation through the literal addition rows defining J.
    known={}
    for idx in range(166,172):
        rows=[r for r in raw['residuals'] if r['label']=='addition'
              and [1,[idx]] in r['terms']]
        if len(rows)!=1:
            raise ValueError(('ambiguous J chain',idx))
        rhs=mod2({tuple(m):a for a,m in rows[0]['terms'] if m!=[idx]})
        reduced=set()
        for m in rhs:
            if len(m)==1 and m[0] in known:
                reduced.symmetric_difference_update(known[m[0]])
            else:
                reduced.symmetric_difference_update({m})
        known[idx]=reduced
    j_mod2=known[171].symmetric_difference({()})
    if j_mod2!={() ,(16,),(17,)}:
        raise ValueError(('wrong J parity',j_mod2))
    # Canonical completeness values; t's parity remains arbitrary.
    receipts=[]
    for tpar in (0,1):
        values={0:tpar,1:0,2:0,4:0,5:1,26:1,171:1,
                179:1,181:1,211:1,223:1,522:1}
        values.update({i:(0 if i==16 else 1) for i in range(16,25)})
        parities=[]
        for atom in atoms:
            value=0
            for m,a in atom.items():
                term=a
                for i in m:
                    term*=values[i]
                value+=term
            parities.append(value%2)
        if sum(parities)%2!=1 or (3+sum(parities))%2:
            raise ValueError(('preferred frame not even',tpar,parities))
        receipts.append({'t_parity':tpar,'atom_parities':parities,
                         'sum_parity':1,'shifted_frame_parity':0})
    print(json.dumps({'status':'passed','source_sha256':hashlib.sha256(data).hexdigest(),
                      'frame_atoms':len(atoms),'old_frame_constant':2,
                      'new_frame_constant':3,
                      'literal_residual_constant_before':old[()],
                      'literal_residual_constant_after':old[()]-1,
                      'J_parity':'1 + stored_a + stored_b = 1 + actual_a + actual_b',
                      'canonical_cases':receipts,
                      'scope':'exact finite frame/J identities; semantic parity choices inherited from MODULAR_PROOF section10'},indent=2))


if __name__=='__main__':
    main()
