#!/usr/bin/env python3
"""Check four literal centered-candidate graphs on an exact polynomial ray.

Usage: python3 verify_all_degree_rays.py /path/to/candidate-json-directory
This finite check supplements centered_degree_proof.tex; it does not by
itself prove a global degree bound or validate the coefficient tuple.
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
        ('strong_center', 358, -9*2**248),
        ('both_centers', 354, 3*2**245),
        ('direct_strong_center', 330, -9*2**220*3**36),
        ('direct_both_centers', 327, 2**218*3**36),
    ]:
        data = json.loads((directory/(name+'.json')).read_text())
        p = exact_ray(data['source'], data['witnesses'])
        if p.degree() != degree or p.LC() != leading:
            raise AssertionError((name, p.degree(), p.LC()))
        report.append({'name':name, 'operations':len(data['source']),
                       'exact_ray_degree':degree,
                       'exact_ray_leading_coefficient':str(leading)})
    print(json.dumps({'specialization': 'all witnesses=t; beta=2,K0=3,MC=5,MF=7',
                      'scope': 'exact ray check; global proof is in centered_degree_proof.tex',
                      'results':report}, indent=2))


if __name__ == '__main__':
    main()
