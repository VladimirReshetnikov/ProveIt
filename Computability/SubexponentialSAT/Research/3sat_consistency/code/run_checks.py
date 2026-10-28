#!/usr/bin/env python3
"""Run every exact checker normally and with -O, retaining both JSON outputs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKS = [('certify.py', True), ('independent_audit.py', True),
          ('independent_joint_audit.py', True), ('check_weight_lower_bound.py', True),
          ('check_inherited_menus.py', False), ('check_structures.py', False),
          ('finite_contraction.py', False), ('check_low_degree.py', True)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT/'replay_results')
    args = parser.parse_args()
    destination = args.output_dir.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    results = []
    for filename, uses_output in CHECKS:
        versions = []
        for optimized in (False, True):
            label = 'optimized' if optimized else 'normal'
            path = destination/(Path(filename).stem+'_'+label+'.json')
            command = [sys.executable] + (['-O'] if optimized else [])
            command += [str(ROOT/'code'/filename)]
            if uses_output:
                command += ['--output', str(path)]
            completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            if completed.returncode:
                raise RuntimeError(filename+' failed: '+completed.stderr+'\n'+completed.stdout)
            if uses_output:
                data = json.loads(path.read_text())
            else:
                data = json.loads(completed.stdout)
                path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
            if data.get('status') != 'PASS':
                raise ValueError(filename+' did not report PASS')
            versions.append(data)
        if versions[0] != versions[1]:
            raise ValueError(filename+' changed under python -O')
        canonical = json.dumps(versions[0],sort_keys=True,separators=(',',':')).encode()
        results.append({'checker':filename,'normal':'PASS','optimized':'PASS',
                        'parsed_outputs_identical':True,
                        'canonical_result_sha256':hashlib.sha256(canonical).hexdigest()})
    summary = {'status':'PASS','checker_count':len(CHECKS),'executions':2*len(CHECKS),
               'all_normal_optimized_outputs_identical':True,'checks':results,
               'scope':'Finite certificates and local prototypes; no full SAT solver or Lean replay'}
    (destination/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()
