#!/usr/bin/env python3
"""Focused verification of the complete fixed-index half-binomial75 proof.

The mathematical proof and independent reviews establish universality.
This program replays the exact source, kernel, compiler and bridge evidence;
it is neither a formal proof nor a materialized enormous universal tuple.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

PAPERS = Path(__file__).resolve().parents[1]
WIP = PAPERS / 'research-wip' / 'native-stream-queue'
sys.path.insert(0, str(WIP))
import complete75_half_binomial as source
import pell_kernel_half_binomial42 as kernel
import complete75_half_binomial_compiler as compiler
import input_bridge_half_binomial75 as bridge


def verify():
    modules = [source, kernel, compiler, bridge]
    results = [module.verify() for module in modules]
    for module, result in zip(modules, results):
        receipt = Path(module.__file__).with_suffix('.json')
        assert json.loads(receipt.read_text()) == json.loads(json.dumps(result)), receipt
    full = results[0]['source']
    assert (full['operations'], full['multiplications'], full['additions_subtractions'],
            full['positive_witnesses'], full['equations']) == (75,41,34,30,19)
    return dict(
        status='PASS_FIXED_RAW_UNIVERSAL75', operations=75, multiplications=41,
        additions_subtractions=34, positive_existential_witnesses=30, equations=19,
        ledger={'outer':19,'strong_half_binomial_kernel':42,'ordinary_input_bridge':14},
        proof='1980/FIXED_RAW_UNIVERSAL_75_PROOF.md',
        source=full,
        component_results=[dict(script=Path(module.__file__).name,
                                source_lf_sha256=hashlib.sha256(Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
                                result=result)
                           for module,result in zip(modules,results)],
        mathematical_review='Three independent full proof/source/default integration reviews PASS without findings',
        theorem='Every recursively enumerable set of positive ordinary inputs has a fixed-numeral positive-witness representation by this75-operation source',
        limits='Mathematical proof with symbolic, sparse, modular and finite checks; not Lean formalized or newly published; astronomical full compiler witnesses are parametric')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==normalized,'complete75 receipt mismatch'
    print(result['status'],result['operations'],result['multiplications'],result['additions_subtractions'],
          result['positive_existential_witnesses'],result['equations'])
