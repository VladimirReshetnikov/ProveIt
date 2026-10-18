#!/usr/bin/env python3
"""Combine the twelve previously justified one-read rho8 role maps with DNE.

The symmetry and contextual-DNE theorems are inherited. Their composition and
exact fine compiler inputs are checked here; state counts require compilation.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--dne-checker',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    ms=importlib.util.spec_from_file_location('rho_dne',args.dne_checker)
    d=importlib.util.module_from_spec(ms);sys.modules[ms.name]=d;ms.loader.exec_module(d)
    spec=d.load_spec()
    fine=json.loads(args.dne_checker.with_name('macro_to_fine.json').read_text())
    logical=spec['ax_rows']('a','old_cache','b','c','u')
    oldbundle=spec['bundle']('a','b','c');paths=d.redexes(oldbundle)
    def renamed(t,mapping):
        return (t[0],renamed(t[1],mapping),renamed(t[2],mapping)) if isinstance(t,tuple) else mapping.get(t,t)
    def leaves(t):
        return leaves(t[1])+leaves(t[2]) if isinstance(t,tuple) else [t]
    variants=[]
    maps=[]
    for perm in itertools.permutations(('a','b','c','u')):
        mapping=dict(zip(('a','b','c','u'),perm))
        row=renamed(logical[1],mapping)
        if Counter(leaves(row))['u']!=1:continue
        assert renamed(row,{v:k for k,v in mapping.items()})==logical[1]
        maps.append(mapping)
        rows=[row,*logical[2:]]
        for mask in (0,32,63):
            bundle=d.normalize(oldbundle,{p for i,p in enumerate(paths) if mask>>i&1})
            macros=[166,121,180,176]+[m for r in rows for m in d.emit(r)]+d.emit(bundle)+d.TAIL
            stack,events=d.execute_macros(macros[:-len(d.TAIL)])
            assert stack==['old_top',logical[0],*rows,bundle]
            assert events[0]==(176,2) and len(events)==2 and events[1][0]==158
            assert macros.count(158)==macros.count(208)==1
            word=''.join(fine[str(m)] for m in macros)
            variants.append(dict(mask=64*len(variants)+32,name='rho8_'+''.join(perm)+'_dne'+str(mask),
                role_map=mapping,dne_mask=mask,fine_AX=word,fine_length=len(word),
                word=macros,logical_rows=rows,bundle=bundle,read_events=events,
                fine_sha256=hashlib.sha256(word.encode()).hexdigest()))
    assert len(maps)==12 and len(variants)==36
    out=dict(status='PASS_RHO8_ROLE_DNE_COMPOSITION',variants=variants,
        count=36,role_maps=maps,scope='Exact source emission and composable inherited theory equivalences; no machine count.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('variants','role_maps')},indent=2))


if __name__=='__main__':main()
