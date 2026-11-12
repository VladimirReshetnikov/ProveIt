"""Untrusted finite-proof translation from scalar UR to Orbit.

The complete checkers do not import this file. Input/output uses the same
certificate dictionary as the checkers. Choose inferred or templates via
argv[1]; the default is inferred. Both the input and output are checked.
"""
from copy import deepcopy
from pathlib import Path
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent

def load(name):
    path = ROOT / 'code' / (name + '.py')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

UR = load('scalar_ur')
Z = ['z']
V = lambda i: ['v', i]
I = lambda n, a, h: ['i', n, a, h]

def refl(a):
    p = ['zero', a, V(0)]
    return ['tr', V(0), p, p]

def sym(a, p):
    return ['tr', V(0), refl(a), p]

def orbit_formula(f, h):
    return ['q', ['=', f, I(V(0), UR.shift(UR.sub(f, Z)), UR.shift(['q', h])[1])]]

def translate(p, mode='inferred'):
    match p:
        case ['hyp', _] | ['zero', _, _] | ['succ', _, _, _]:
            return deepcopy(p)
        case ['qe', t, p, q]:
            return ['qe', t, translate(p, mode), translate(q, mode)]
        case ['de', a, p, q]:
            return ['de', a, translate(p, mode), translate(q, mode)]
        case ['di', b, t, p]:
            return ['di', b, t, translate(p, mode)]
        case ['ur', f, h, t, p]:
            proof = translate(p, mode)
            op = ['orbit', orbit_formula(f, h), proof] if mode == 'inferred' else ['orbit', f, h, proof]
            initial = UR.sub(f, Z)
            base = sym(I(Z, initial, h), ['zero', initial, h])
            return ['qe', t, op, base]
        case ['tr', a, p, q]:
            return ['tr', a, translate(p, mode), translate(q, mode)]
        case _:
            raise ValueError('Unknown UR proof')

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'inferred'
    if mode not in ('inferred', 'templates'):
        raise ValueError('Mode must be inferred or templates')
    cert = json.load(sys.stdin)
    UR.check(cert)
    cert['proof'] = translate(cert['proof'], mode)
    load('orbit_' + mode).check(cert)
    print(json.dumps(cert, separators=(',', ':')))
