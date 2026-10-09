"""Seeded, literal graph audits. No native knot-exterior or Regina claim."""
import argparse
from collections import Counter
from hashlib import sha256
import json
import platform
import random
from common import ROOT, random_case, literal, literal_signed
from sparse_incidence.api import analyze
from sparse_incidence.signed import analyze_signed, verify_signed
from sparse_incidence.verify import verify
from sparse_incidence.codec import save


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cases',type=int,default=1000)
    p.add_argument('--output',default=str(ROOT/'results/validation.json'))
    args=p.parse_args()
    rng=random.Random(261008490)
    rows=[];operations=Counter()
    for i in range(args.cases):
        size,pairs,ports=random_case(rng,max_size=50,max_rank=10)
        case=(size,pairs,ports)
        expected=literal(*case)
        answer=analyze(*case,record_certificate=True)
        if dict(answer['histogram']) != expected or not verify(*case,answer['certificate']):
            raise AssertionError(('incidence mismatch',case))
        for proof in [answer['certificate']['baseline']]+[
                x['proof'] for x in answer['certificate']['union_proofs']]:
            operations.update(event['op'] for event in proof['operations'])
        signed=[row+[rng.randrange(2)] for row in pairs]
        oriented=analyze_signed(size,signed,ports,record_certificate=True)
        if ({m:[a,b] for m,a,b in oriented['histogram']} != literal_signed(size,signed,ports)
                or not verify_signed(size,signed,ports,oriented['certificate'])):
            raise AssertionError(('signed mismatch',case))
        rows.append(dict(size=size,pairings=pairs,ports=ports,
                         histogram=answer['histogram'],stats=answer['stats'],
                         signed_pairings=signed,signed_histogram=oriented['histogram'],
                         signed_stats=oriented['stats']))
    data=dict(schema='sparse-incidence-validation-v1',seed=261008490,cases=args.cases,
              python=platform.python_version(),platform=platform.platform(),
              failures=0,operations=dict(operations),cases_data=rows,
              scope='Literal interval graphs and binary covers; not whole-knot queries.')
    save(args.output,data)
    print(json.dumps({k:v for k,v in data.items() if k!='cases_data'},indent=2))

if __name__=='__main__':main()
