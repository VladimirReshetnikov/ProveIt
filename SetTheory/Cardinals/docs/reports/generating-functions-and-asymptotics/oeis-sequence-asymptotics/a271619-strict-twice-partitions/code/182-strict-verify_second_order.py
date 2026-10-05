#!/usr/bin/env python3
"""Read-only exact verification of the finite second-correction supplement."""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify
import second_order
ROOT=verify.ROOT
PINS={'data/SECOND_ORDER_PROVENANCE.json': 'd4909cffa2ed5616d4c068cf8d7db77d2c0a2f4be0713c48ce11085e0100f603', 'data/references/independent_a2_check_frozen.json': 'a647c9a89b115f5c1da01594917840c91b9e4d8ca25ba566fa3e5d368b99c0c5', 'data/references/independent_a2_check_frozen.py': 'aa5940e010fd22c8b0c5409e3f3d00b4c4e9a0839aed65d5943a87275e0588a6', 'data/references/second_order_root_brackets.json': '373b620b74938e18e211b5748e244fd8bd20f9f7bc3965f82ad4cb062c9eaab9'}


def references():
    for name,digest in PINS.items():
        verify.need(hashlib.sha256(verify.read(ROOT/name)).hexdigest()==digest,
                    'second-order reference modified: '+name)
    return dict(PINS)


def derive():
    references()
    result=second_order.derive()
    root=verify.load_certificate(ROOT/'data/references/second_order_root_brackets.json')
    independent=verify.load_certificate(ROOT/'data/references/independent_a2_check_frozen.json')
    names={8:'Q3hat_squared',10:'Q2_squared_Q3hat',12:'Q2_fourth'}
    for weight in (8,10,12):
        actual=result['brackets'][str(weight)]
        source=root[str(weight)]
        other=independent[names[weight]]
        verify.same(actual['basis_E2_E4_E6'],source['basis'])
        verify.same(actual['coefficients'],source['coefficients'])
        verify.same(actual['initial_determinant'],source['initial_minor_determinant'])
        verify.same(actual['q_coefficients_checked'],source['terms_verified'])
        verify.same(actual['basis_E2_E4_E6'],other['basis'])
        verify.same(actual['coefficients'],other['coefficient'])
        verify.same(actual['initial_determinant'],other['initial_determinant'])
        verify.same(actual['q_coefficients_checked'],other['checked_coefficients'])
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data/second_order_certificate.json')
    args=parser.parse_args()
    try:
        result=derive()
        verify.same(result,verify.load_certificate(args.data))
        print(verify.canonical({'status':'PASS','report':182,
            'certificate_sha256':hashlib.sha256(verify.canonical(result)).hexdigest(),
            'weights':[8,10,12],'q_coefficients_checked':21,
            'partitions_enumerated':result['partitions_enumerated'],
            'A2_B2_algebra_exact':True,'scope':result['scope']}).decode(),end='')
    except (ValueError,RuntimeError,TypeError,KeyError,IndexError,OSError) as exc:
        print('SECOND-ORDER VERIFICATION FAILED: '+str(exc),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
