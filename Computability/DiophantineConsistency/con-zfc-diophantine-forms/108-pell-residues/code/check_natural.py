#!/usr/bin/env python3
"""Replay the inherited independent natural projection without writing inputs."""
from pathlib import Path
import argparse
import importlib.util
import json


def main(checker_path, source_path, target_path):
    spec = importlib.util.spec_from_file_location('independent_natural_projection', checker_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    read = lambda name: json.loads(Path(name).read_text())
    target_path = Path(target_path)
    result, coefficients = module.verify(read(source_path),
        read(target_path/'equation.json'), read(target_path/'elimination_certificate.json'))
    if coefficients != read(target_path/'expanded_polynomial.json')['terms']:
        raise ValueError('Delivered collected coefficients do not match')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('checker', type=Path)
    parser.add_argument('source', type=Path)
    parser.add_argument('target', type=Path)
    args = parser.parse_args()
    print(json.dumps(main(args.checker,args.source,args.target), indent=2, sort_keys=True))
