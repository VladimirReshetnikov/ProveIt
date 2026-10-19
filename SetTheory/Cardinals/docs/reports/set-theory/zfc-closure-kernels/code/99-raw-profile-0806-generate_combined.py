#!/usr/bin/env python3
"""Exact AX targets combining proved equality orientations and bundle DNE.

These are source-level research targets, not certified Turing machines.
Inputs are the two explicitly attributed incoming research packages.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT = HERE / 'build/zfc-below245-source-search-20261018'

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def reverse_eq(t):
    if not isinstance(t, tuple):
        return t
    k,a,b=t
    if k=='eq': return (k,b,a)
    if k=='rel': return t
    if k=='all': return (k,a,reverse_eq(b))
    assert k=='imp'
    return (k,reverse_eq(a),reverse_eq(b))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package',type=Path,default=DEFAULT)
    p.add_argument('--output',type=Path,default=HERE/'combined_variants.json')
    p.add_argument('--all-dne',action='store_true')
    args=p.parse_args()
    enc=args.package/'work/theory_encoding'
    v=load(enc/'check_dne_variants.py','combined_dne')
    spec=v.load_spec()
    original_rows=spec['ax_rows']('a','old_cache','b','c','u')
    original_bundle=spec['bundle']('a','b','c')
    mapping=json.loads((enc/'macro_to_fine.json').read_text())
    fine=lambda ms: ''.join(mapping[str(m)] for m in ms)
    masks=range(64) if args.all_dne else (32,63,0)
    rows=[]
    for orient,bits in enumerate(itertools.product((0,1),repeat=5)):
        anchor,flip3,flip5,flip7,eqv=bits
        changed=[]
        for number,t in zip((8,7,6,5,4,3,2,1),original_rows[1:]):
            a=reverse_eq(t) if anchor else t
            if (number==3 and flip3) or (number==5 and flip5): a=reverse_eq(a)
            if number==7 and flip7:
                assert a[0]=='imp' and a[2][0]=='imp' and a[2][2][0]=='eq'
                a=('imp',a[1],('imp',a[2][1],reverse_eq(a[2][2])))
            changed.append(a)
        # The only explicit equality atoms in the bundle belong to equality vacuity.
        bundle=reverse_eq(original_bundle) if eqv else original_bundle
        redex=v.redexes(bundle)
        assert len(redex)==6
        for dne in masks:
            normalized=v.normalize(bundle,{a for i,a in enumerate(redex) if dne>>i&1})
            word=[166,121,180,176]+[m for t in changed for m in v.emit(t)]+v.emit(normalized)+v.TAIL
            stack,events=v.execute_macros(word[:-5])
            assert stack==['old_top',original_rows[0],*changed,normalized]
            assert events==[(176,2),(158,4)]
            assert normalized[0]=='imp'
            s=fine(word)
            assert len(s)==1270-18*dne.bit_count()
            rows.append(dict(mask=10000+64*orient+dne,
                name=f'eq{orient:02d}_dne{dne:02d}',equality_bits=list(bits),dne_mask=dne,
                logical_rows=changed,bundle=normalized,word=word,fine_AX=s,
                fine_length=len(s),macro_length=len(word),
                fine_sha256=hashlib.sha256(s.encode()).hexdigest(),
                proof_steps=['Anchored equality-axiom replacement; arbitrary matrix codes unchanged',
                             'Common-core double-negation equivalence in fixed bundle contexts']))
    assert len({r['fine_AX'] for r in rows})==len(rows)
    out=dict(status='PROVED_SOURCE_FAMILY_REQUIRES_BINARY_COMPILATION',
        source_attribution=['Mira-Cult source calculus; Jeff Ketchersid specification',
          'ProveIt incoming zfc-below245-research-20261018: anchored equality orientations',
          'ProveIt incoming zfc-below245-source-search-20261018: bundle DNE and macro bridge'],
        equality_orientation_count=32,dne_masks=list(masks),variants=rows)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps(dict(status=out['status'],variants=len(rows),output=str(args.output),
        minimum_fine_length=min(r['fine_length'] for r in rows))))

if __name__=='__main__': main()
