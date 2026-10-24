#!/usr/bin/env python3
"""Check exact untouched source boundaries and finite controls of branch factoring."""
import argparse
from hashlib import sha256
from itertools import product
import json
from math import prod
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    original=(here/"direct_source.py").read_text()
    changed=(here/"direct_source_factored.py").read_text()
    before="    pq = self.sum([square(p), square(q)])"
    after="    carrier = add("
    require(original[original.index("def source_pair_calculus("):original.index(before)]
            ==changed[changed.index("def source_pair_calculus("):changed.index(before)],
            "C222 constructor prefix changed")
    require(original[original.index(after):]==changed[changed.index(after):],
            "eleven-coordinate row suffix changed")
    cases=0
    for p,q,v,c1,c2,b,g in product(range(-1,2),repeat=7):
        C=p*p+q*q
        A=v*(v-c1)*(v-c2)
        B=(v-b)**2+g*g
        old=(C+v*v)*prod(C+(v-c)**2 for c in (c1,c2))*(C+B)
        new=C+A*A*B
        require(old>=0 and new>=0,"nonnegative branch invariant")
        require((old==0)==(new==0),"axiom zero-set factoring")
        for mp,gen in ((0,1),(1,0),(1,1),(4,9)):
            for residual_square in (0,1,4):
                require((old*mp*gen+residual_square==0)
                        ==(new*mp*gen+residual_square==0),"whole source zero-set factoring")
        cases+=1
    result={"status":"PASS","unchanged_constructor_prefix":True,
            "unchanged_eleven_coordinate_suffix":True,
            "axiom_factoring_controls":cases,
            "whole_source_controls":cases*12,
            "optimized_python":not __debug__,
            "scope":"Exact copied-source boundaries and finite controls; universal zero-set equivalence is proved in factored_source_proof.md.",
            "sha256":{name:sha256((here/name).read_bytes()).hexdigest() for name in
                      ("direct_source.py","direct_source_factored.py","audit_factored_source.py")}}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
