#!/usr/bin/env python3
"""Independent exact univariate polynomial checks of integer12 saturation.

Usage: python3 verify_integer12_saturated_ray.py CANDIDATE_DIRECTORY
The directory contains rational.json and integral.json in the literal
integer arithmetic DAG format. This is a finite transcription check,
supplementing the global homogeneous-form proof.
"""
import hashlib
import json
from pathlib import Path
import sys
from polynomial_ray import Poly


def replay(data):
    constants = {'beta':2, 'K0':3, 'MC':5, 'MF':7, 'cone_A':11, 'cone_B':13}
    env = []
    operations = 0
    for row in data['nodes']:
        kind = row[0]
        if kind == 'variable':
            value = Poly([0,1])
        elif kind == 'integer':
            value = Poly([row[1]])
        elif kind == 'coefficient':
            value = Poly([constants[row[1]]])
        else:
            left, right = env[row[1]], env[row[2]]
            if kind == 'add':
                value = left+right
            elif kind == 'sub':
                value = left-right
            elif kind == 'mul':
                value = left*right
            else:
                raise ValueError(kind)
            operations += 1
        env.append(value)
    prefix = {key:env[data['named_registers'][key]].degree()
              for key in ['Dt','U','Df','delta','V','S','Ac','fs','fc','fa','fb','Pe']}
    return env[data['output']], operations, prefix


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    directory = Path(sys.argv[1])
    result = []
    for name, expected_degree, leading, formula in [
        ('rational',1084,2**1768*3**760,'2^1144*3^760*beta^624 at beta=2'),
        ('integral',1280,2**2048*3**880,'2^1320*3^880*beta^728 at beta=2'),
    ]:
        raw = (directory/(name+'.json')).read_bytes()
        data = json.loads(raw)
        out, ops, prefix = replay(data)
        if out.degree() != expected_degree or out.LC() != leading:
            raise AssertionError((name,out.degree(),out.LC()))
        if ops != data['operations']:
            raise AssertionError((ops,data['operations']))
        result.append({'variant':name,'graph_sha256':hashlib.sha256(raw).hexdigest(),
                       'operations':ops,'exact_ray_degree':out.degree(),
                       'expected_leading_coefficient':formula,
                       'leading_coefficient_bits':out.LC().bit_length(),
                       'leading_coefficient_matches':True,
                       'exact_ray_register_degrees':prefix})
    print(json.dumps({'specialization':'all 12 witnesses=t; beta=2,K0=3,MC=5,MF=7,cone_A=11,cone_B=13',
                      'scope':'one exact polynomial ray; global bound proved separately',
                      'results':result},indent=2))


if __name__ == '__main__':
    main()
