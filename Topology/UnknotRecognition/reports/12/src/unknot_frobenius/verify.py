"""Verify an algebraic succinct-interface certificate, NOT a knot verdict.

Usage: PYTHONPATH=src python -m unknot_frobenius.verify certificate.json
"""
from __future__ import annotations
import argparse,json,pathlib
from .tensors import TensorVector,TensorTerm,tensor_interface
from .blocks import matrix


def verify_spec(spec):
    if spec.get('schema')!='unknot-frobenius-interface-v1':
        raise ValueError('unsupported certificate schema')
    b,m=spec['variables'],spec['modes']
    if type(b) is not int or not 0<=b<=12 or type(m) is not int or not 0<=m<=4096:
        raise ValueError('certificate exceeds verifier parameter limits')
    def vectors(key):
        raw=spec[key]
        if not isinstance(raw,list) or not 1<=len(raw)<=32:
            raise ValueError('invalid interface dimension')
        answer=[]
        for terms in raw:
            if not isinstance(terms,list) or len(terms)>128:
                raise ValueError('invalid tensor term count')
            answer.append(TensorVector(b,m,tuple(TensorTerm(t['weight'],tuple(tuple(pair) for pair in t['factors'])) for t in terms)))
        return tuple(answer)
    data=tensor_interface(vectors('u_columns'),vectors('v_rows'),vectors('c_columns'),vectors('d_rows'),matrix(spec['e']))
    result=data.evaluate(b)
    expected=matrix(spec['expected_schur'])
    if result!=expected:
        raise ValueError('claimed Schur complement does not match recomputation')
    return dict(algebraic_certificate_verified=True,represented_dimension=str(1<<m),
                schur=result,core=data.core,unknot_verdict=None,
                scope='Exact structured same-matching block identity; not a complete topological certificate.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=pathlib.Path);args=ap.parse_args()
    try:
        if args.certificate.stat().st_size>8_000_000:
            raise ValueError('certificate file exceeds size limit')
        result=verify_spec(json.loads(args.certificate.read_text()))
    except (OSError,ValueError,TypeError,KeyError,MemoryError) as exc:
        ap.exit(1,f'certificate rejected: {exc}\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
