#!/usr/bin/env python3
"""Replay the retained coefficient-three refutation without modifying inputs."""
import argparse
import importlib.util
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='optional fresh JSON receipt')
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled; do not use Python -O.')
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        'retained_coefficient3_verifier', here / 'verify_primitive.py')
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    result = verifier.verify(here / 'primitive_proof.json')
    assert result['certificate_sha256'] == (
        'baf316dce45568036fd803382b30ae2669eb504222a39a6be1f3abcad77dcb83')
    assert result['arithmetic_terms'] == 116171
    assert result['primitive_proof_steps'] == 73393
    assert result['rule_counts'] == {
        'rho8': 34888, 'mp': 38503, 'gen': 1, 'head5_0_1': 1}
    assert result['maximum_term_depth'] == 36
    assert result['final_conclusion'] == 1
    text = json.dumps(result, indent=2) + '\n'
    if args.output is not None:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
