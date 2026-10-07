#!/usr/bin/env python3
"""Run all checks twice in each interpreter mode; require byte-identical JSON."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.metadata
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from validation import require, write_json, require_diagnostic_digit_limit

ROOT=Path(__file__).resolve().parent
OUTPUTS=['hierarchy_coefficients.json','check_results.json','rational_checks.json',
         'negative_controls.json','recovery_example.json']


def run_one(mode, directory):
    flags=['-O'] if mode.startswith('optimized') else []
    def run(script,*args):
        completed=subprocess.run([sys.executable,*flags,str(ROOT/script),*map(str,args)],
                                 cwd=directory,capture_output=True,text=True,check=False)
        if completed.returncode:
            raise ArithmeticError(f'{script} failed: {completed.stderr}')
    run('derive_hierarchy.py','--output',directory/OUTPUTS[0])
    run('check_hypergraph.py','--coefficients',directory/OUTPUTS[0],
        '--output',directory/OUTPUTS[1])
    run('rational_checks.py','suite','--output',directory/OUTPUTS[2])
    run('negative_controls.py','--output',directory/OUTPUTS[3])
    run('rational_checks.py','recover','2','25','--output',directory/OUTPUTS[4])
    return {name:(directory/name).read_bytes() for name in OUTPUTS}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=ROOT/'results')
    args=parser.parse_args()
    require_diagnostic_digit_limit()
    expected={'sympy':'1.14.0','mpmath':'1.3.0'}
    for package,version in expected.items():
        require(importlib.metadata.version(package)==version,
                f'{package} must be version {version}; install requirements.txt')
    modes=['normal-1','normal-2','optimized-1','optimized-2']
    with tempfile.TemporaryDirectory() as temporary:
        base=Path(temporary)
        directories=[base/mode for mode in modes]
        for directory in directories:
            directory.mkdir()
        with ThreadPoolExecutor(max_workers=2) as executor:
            results=list(executor.map(run_one,modes,directories))
        for name in OUTPUTS:
            require(all(result[name]==results[0][name] for result in results[1:]),
                    f'Non-deterministic output: {name}')
        args.output_dir.mkdir(parents=True,exist_ok=True)
        for name in OUTPUTS:
            (args.output_dir/name).write_bytes(results[0][name])
        receipt={'status':'PASS','interpreter_modes':modes,
                 'all_json_byte_identical':True,'dependencies':expected,
                 'outputs':{name:hashlib.sha256(results[0][name]).hexdigest() for name in OUTPUTS}}
        write_json(args.output_dir/'reproduction_receipt.json',receipt)
    print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
