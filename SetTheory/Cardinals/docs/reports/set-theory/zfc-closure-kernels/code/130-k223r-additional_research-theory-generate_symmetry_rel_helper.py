#!/usr/bin/env python3
"""Emit K224 REL-helper proofs with primitive symmetry and no Euclidean row.

Adapted from K224 generate_rel_helper_certificate.py and attributed Source116
proof constructors.  The independent checker imports none of these utilities.
This program changes only the equality bootstrap: the retained auxiliary
profile transport, membership-defined equality, and K interpretation are the
ones used by Source116/K224.
"""
from __future__ import annotations
import argparse
from functools import cache
import hashlib
import importlib
import json
from pathlib import Path
import sys

e = g = None

def rel_code(a, b):
    return 4 * ((a+b)*(a+b+1)//2+b)+1

def helper(a, b):
    atom=e.Eq(a,b)
    return e.P('REL_HELPER',e.I(atom,e.Q(rel_code(a,b),atom)))

@cache
def primitive_sym(a,b):
    return e.P('SYM',e.I(e.Eq(a,b),e.Eq(b,a)))

def eq_to_E(a,b):
    atom=e.Eq(a,b)
    if a==b:
        return e.mp(e.k(g.E(a,b),atom),g.e_refl(a))
    z=rel_code(a,b)
    parts=[]
    for out in (False,True):
        forward=g.left(a,b,z) if out else g.right(a,b,z)
        reverse=g.left(b,a,z) if out else g.right(b,a,z)
        body=g.body(a,b,z,out)
        implication=g.prop(e.I(atom,body),forward,primitive_sym(a,b),reverse)
        parts.append(g.prop(e.I(atom,e.Q(z,body)),helper(a,b),e.mono(z,implication)))
    initial=g.prop(e.I(atom,g.Ez(a,b,z)),*parts)
    return g.prop(e.I(atom,g.E(a,b)),initial,g.aux(a,b,z,g.weq(a,b)))

@cache
def normalize_symmetry(p):
    if p.rule in ('SYM','Sym'):
        a,b=p.form[1][1:]
        return primitive_sym(a,b)
    if p.rule=='MP': return e.mp(*(normalize_symmetry(q) for q in p.args))
    if p.rule=='GEN': return e.gen(p.args[0],normalize_symmetry(p.args[1]))
    if p.rule in ('rho7','V_eq'):
        raise ValueError('forbidden primitive dependency: '+p.rule)
    return p

def main():
    global e,g
    parser=argparse.ArgumentParser()
    parser.add_argument('--source116-proofs',type=Path,required=True,
                        help='Path to K224 portable/theory/source116/proofs')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('symmetry_rel_helper_certificate.json'))
    args=parser.parse_args()
    provider=args.source116_proofs.resolve()
    sys.path.insert(0,str(provider))
    e=importlib.import_module('equality_certificates')
    g=importlib.import_module('indiscernibility_certificates')
    roots={}
    for x in (0,1,7,999):roots[f'primitive_sym/{x}/0']=primitive_sym(x,0)
    for x,y in ((0,0),(0,1),(1,0),(1,1),(2,7),(100,999)):
        bridge=eq_to_E(x,y)
        roots[f'eq_to_E/{x}/{y}']=bridge
        roots[f'exists_E/{x}/{y}']=e.mp(e.emono(x,bridge),e.rho1(x,y))
        k=g.weq(x,y)
        roots[f'E_vacuity/{x}/{y}/{k}']=g.e_vac(x,y,k)
        for z in sorted({0,x,y,k}):
            roots[f'E_in/{x}/{y}/{z}']=g.e_rel(x,y,z)
            roots[f'E_out/{x}/{y}/{z}']=g.e_rel(x,y,z,True)
    for x,y,z in ((0,0,0),(0,1,1),(2,7,g.weq(2,7)),(999,0,100)):
        roots[f'E_rho7/{x}/{y}/{z}']=g.e_rho7(x,y,z)
    roots={name:normalize_symmetry(p) for name,p in roots.items()}
    if any(e.assumptions(p) for p in roots.values()):raise ValueError('open root')
    data=e.export(roots)
    data['format']='symmetry-rel-helper-bootstrap-v1'
    data['scope']='Actual Rel(a,b)-code helper and primitive symmetry; no primitive rho7 or V_eq. TAUT abbreviates the retained rho8/rho6 classical basis. Uniform K matrix/private-code coupling is the inherited K224 argument.'
    data['providers']={name:hashlib.sha256((provider/name).read_bytes()).hexdigest() for name in ('equality_certificates.py','indiscernibility_certificates.py')}
    args.output.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps({'certificate':str(args.output),'closed_roots':len(roots),'proof_nodes':len(data['proof_nodes']),'formulas':len(data['formulas']),'providers':data['providers']},indent=2))

if __name__=='__main__':main()
