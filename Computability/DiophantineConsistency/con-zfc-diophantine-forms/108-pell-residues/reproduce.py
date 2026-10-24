#!/usr/bin/env python3
"""Rebuild every new equation from bundled, pinned source and compare outputs."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from release_support import command, compare_json, parent_workspace, require


def reproduce(output):
    output = Path(output).resolve()
    require(not output.exists() or not any(output.iterdir()), 'Output directory must be empty')
    output.mkdir(parents=True,exist_ok=True)
    result = {'status':'pass','optimized_python':not __debug__}
    with parent_workspace() as parent:
        result['natural_builder'] = command(parent/'code/build_modular.py',
                                             '--output',output/'natural')
        for name in ('source655','natural395','natural394'):
            filenames = ('equation.json','expanded_polynomial.json')
            if name != 'source655':
                filenames += ('elimination_certificate.json',)
            for filename in filenames:
                compare_json(output/'natural'/name/filename, ROOT/'equations'/name/filename)
        for name, cap in (('integer663',16),('integer687',4)):
            result[name] = command(ROOT/'code/integer_domain/build_mixed.py',
                '--source',output/'natural/source655/equation.json',
                '--output',output/name,'--cap',cap,
                '--bound-certificate',ROOT/'certificates/integer_domain_bounds.json')
            for filename in ('source.json','guarded.json','domain_certificate.json',
                             'equation.json','expanded_polynomial.json',
                             'elimination_certificate.json','METRICS.json'):
                compare_json(output/name/filename, ROOT/'equations'/name/filename)
    secondary = ROOT/'supplemental/integer12'
    for variant, degree in (('integral',2400),('rational',2368)):
        filename = f'centered12_{variant}{degree}.json'
        result[f'twelve_{variant}'] = command(secondary/'build_centered12.py',
             '--variant',variant,'--optimize-order','--output',output/filename)
        compare_json(output/filename,secondary/'equations'/filename)
    (output/'REPRODUCTION_RECEIPT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    print(json.dumps(reproduce(args.output),indent=2,sort_keys=True))
