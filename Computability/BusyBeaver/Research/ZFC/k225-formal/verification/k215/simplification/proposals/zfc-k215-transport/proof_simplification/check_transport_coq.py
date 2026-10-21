#!/usr/bin/env python3
"""Compile and independently kernel-check the generic Coq/Rocq transport lemma."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--coqc', type=Path, default=Path('coqc'))
ap.add_argument('--coqchk', type=Path, default=Path('coqchk'))
a = ap.parse_args()
here = Path(__file__).resolve().parent
compiler = str(a.coqc)
checker = str(a.coqchk)
proc = subprocess.run([compiler, 'PositiveStuttering.v'], cwd=here,
                      capture_output=True, text=True)
(here / 'positive_stuttering_coq_kernel.log').write_text(proc.stdout + proc.stderr)
assert proc.returncode == 0, proc.stdout + proc.stderr
assert 'Closed under the global context' in proc.stdout
check = subprocess.run([checker, '-silent', 'PositiveStuttering'], cwd=here,
                       capture_output=True, text=True)
(here / 'positive_stuttering_coqchk.log').write_text(check.stdout + check.stderr)
assert check.returncode == 0, check.stdout + check.stderr
source = here / 'PositiveStuttering.v'
r = {
  'schema': 'positive-stuttering-coq-v1', 'status': 'PASS_CLOSED',
  'compiler': subprocess.check_output([compiler, '--version'], text=True).strip(),
  'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
  'source_bytes': source.stat().st_size, 'endpoint': 'halts_iff', 'axioms': [],
  'coqc_returncode': proc.returncode, 'coqchk_returncode': check.returncode,
  'coqchk_status': 'PASS',
  'note': 'Checked using the compiler version recorded above; not a replay of ProveIt K215.'
}
(here / 'positive_stuttering_coq_receipt.json').write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps(r, indent=2))
