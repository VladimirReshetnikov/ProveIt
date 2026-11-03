#!/usr/bin/env python3
"""Finite residue checks for a source review; no Lean replay."""
from hashlib import sha256
from math import gcd
from pathlib import Path
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')

ROOT = Path(__file__).resolve().parents[2]
FILES = {
    'research/ordinary12-ipra-bridge/compact44-controller-unit-prototype/ArithmeticConstructionUnitCompact44.lean':
        '3f72112b29fe4d70b7896f541efbe9503b89a364de93137fcda4168288f970e9',
    'research/ordinary12-ipra-bridge/compact44-controller-unit-prototype/observations/compile.log':
        '02b33f12760f2783adb8aa4dea72ba2b75a3f00bc6dbc79bf9649b001bd2bfb1',
    'research/ordinary12-ipra-bridge/compact44-controller-unit-prototype/observations/terminal.json':
        'f0df37e846be637ea634473271e7686029b565c794e86999d00e868958d5e7c8',
    'research/ordinary12-ipra-bridge/compact44-controller-data-prototype/ArithmeticControllerDataCompact44.lean':
        '8f28cce9e32b29bd3fd70ef193c46730aee3b2664e92037ce594ce0638c2f02c',
    'Lean/DiophantineConsistency/ArithmeticControllerLift.lean':
        '5526db4fc7b6cc5a445ef913a0b6581a9e5abac1986e487862e0de2cb2c7dfa3',
}

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def check_sources():
    for path, expected in FILES.items():
        require(sha256((ROOT / path).read_bytes()).hexdigest() == expected,
                'source or receipt changed: ' + path)

check_sources()
d, p, k = 590069, 581197, 284898815895
modulus = d*p
b = pow(2, d, modulus)
rho = pow(2, 67*1063, modulus)
square = b*b % modulus
gamma = rho * (square - 1) * (1 + b*(k+b)) % modulus
require((modulus, b, rho, square, gamma) ==
        (342946332593, 290226301192, 298529384010, 201792753151, 306697999258),
        'intermediate residues')
require(1 <= square < modulus, 'positive square residue for subtraction')
require(pow(b, p, modulus) == b, 'Frobenius fixed point')
require(pow(gamma, p-1, modulus) == 1, 'unit power')
require(gcd(gamma, modulus) == 1, 'external unit check')
receipt = json.loads((ROOT / 'research/ordinary12-ipra-bridge/compact44-controller-unit-prototype/observations/terminal.json').read_text())
require(receipt['exit_code'] == 0 and receipt['object_sha256'] ==
        'f2cc7d761a84af68e602249d2db96cad8470ec087a6517d00356842bf9a1adf9',
        'author compile observation')
check_sources()
print(json.dumps({'status':'PASS_CONDITIONAL_UNIT_SOURCE_REVIEW',
                  'L_B_rho_B2_Gamma':[modulus,b,rho,square,gamma],
                  'frob':pow(b,p,modulus), 'gamma_power':pow(gamma,p-1,modulus),
                  'scope':'external finite arithmetic and source inspection; no Lean replay'},
                 sort_keys=True))
