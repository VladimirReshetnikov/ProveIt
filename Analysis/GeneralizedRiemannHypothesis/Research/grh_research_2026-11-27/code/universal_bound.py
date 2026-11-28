#!/usr/bin/env python3
"""Reference finite enumeration of the sharp local fewnomial constant.

The search can be extremely large.  A transparent profile budget is applied
before starting.  Increase --max-profiles explicitly when a larger search
is intended.  This budget affects runtime, never the mathematical answer.
"""
import argparse
import json
import math
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from sparse_disk import cutoff, is_prime, lenstra_cutoff, solve


def universal(p,t,depth,max_profiles=100000):
    if not is_prime(p) or t < 1 or max_profiles < 1:
        raise ValueError("p must be prime; t and max_profiles must be positive")
    deep = depth=="open" or Fraction(depth)>Fraction(1,p-1)
    bounds = cutoff(p,t) if deep else lenstra_cutoff(p,t,depth)
    modulus = bounds["residue_modulus"]
    count = math.comb(modulus+t-1,t)
    if count > max_profiles:
        raise ValueError(f"The proved enumeration needs {count} residue profiles; "
                         f"the requested budget is {max_profiles}. "
                         "No partial search or approximate answer was returned.")
    best = -1
    witness = None
    distribution = Counter()
    for residues in combinations_with_replacement(range(modulus),t):
        seen = Counter()
        E = []
        for a in residues:
            E.append(a+modulus*seen[a])
            seen[a] += 1
        E.sort()
        answer = solve(E,p,depth,False)
        value = answer["maximum"]
        distribution[value] += 1
        if value > best:
            best = value
            witness = E
    return {"p":p,"t":t,"depth":str(depth),"maximum":best,
            "residue_precision":bounds["residue_precision"],"modulus":modulus,
            "profiles":count,"distribution":dict(sorted(distribution.items())),
            "attaining_support":witness,
            "witness":solve(witness,p,depth,True)}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime",type=int,required=True)
    parser.add_argument("--terms",type=int,required=True)
    parser.add_argument("--depth",default="open")
    parser.add_argument("--max-profiles",type=int,default=100000)
    args=parser.parse_args()
    try:
        result=universal(args.prime,args.terms,args.depth,args.max_profiles)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(result,indent=2))
