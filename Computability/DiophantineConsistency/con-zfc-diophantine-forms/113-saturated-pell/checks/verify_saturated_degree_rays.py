#!/usr/bin/env python3
"""Exact degree-ray check for four literal saturated candidate graphs.

Usage: python3 verify_saturated_degree_rays.py CANDIDATE_JSON_DIRECTORY
The global degree proof is saturated_degree_proof.tex. This script only
checks one exact integer-polynomial specialization of each graph.
"""
import json
from pathlib import Path
import sys
from polynomial_ray import exact_ray


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    directory = Path(sys.argv[1])
    report = []
    for name, degree, leading in [
        ('saturated_upper', 283, 2**192),
        ('saturated_sharp', 278, 2**188),
        ('direct_saturated_upper', 258, 2**167*3**29),
        ('direct_saturated_sharp', 254, 2**164*3**28),
    ]:
        data = json.loads((directory/(name+'.json')).read_text())
        p = exact_ray(data['source'], data['witnesses'])
        if p.degree() != degree or p.LC() != leading:
            raise AssertionError((name, p.degree(), p.LC()))
        report.append({'name':name, 'operations':len(data['source']),
                       'exact_ray_degree':degree,
                       'exact_ray_leading_coefficient':str(leading)})
    print(json.dumps({'specialization': 'all witnesses=t; beta=2,K0=3,MC=5,MF=7',
                      'scope': 'exact ray check; global proof is saturated_degree_proof.tex',
                      'results':report}, indent=2))


if __name__ == '__main__':
    main()
