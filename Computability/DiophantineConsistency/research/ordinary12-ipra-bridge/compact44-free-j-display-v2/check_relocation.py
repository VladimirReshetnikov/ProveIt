#!/usr/bin/env python3
"""Record checks after moving the clarified packet to its own directory."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
here = Path(__file__).resolve().parent
out = here / 'observations' / 'relocation-check01'
out.mkdir(parents=True, exist_ok=False)
results = {}
for variant, rebuilt, suffix in [('94', 'build-attempt11', '94'), ('95', 'build-attempt12', '')]:
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(here / 'check_display.py'),
                          '--variant', variant], cwd=here, text=True, capture_output=True, timeout=180)
    (out / f'{variant}.stdout').write_text(run.stdout)
    (out / f'{variant}.stderr').write_text(run.stderr)
    if run.returncode or run.stderr or json.loads(run.stdout)['status'] != 'EXTERNAL_TEX_PDF_DISPLAY_CHECK_PASS':
        raise RuntimeError('display check failed; observation retained')
    hashes = {}
    for ext in ('tex', 'pdf'):
        canonical = (here / f'equation{suffix}.{ext}').read_bytes()
        if canonical != (here / rebuilt / f'equation.{ext}').read_bytes():
            raise RuntimeError(f'v2-local rebuild mismatch: {variant} {ext}')
        hashes[ext] = sha256(canonical).hexdigest()
    results[variant] = {'display_check_exit': run.returncode, 'local_rebuild': rebuilt,
                        'canonical_sha256': hashes,
                        'stdout_sha256': sha256(run.stdout.encode()).hexdigest(),
                        'stderr_sha256': sha256(run.stderr.encode()).hexdigest()}
receipt = {'status': 'RELOCATED_EXTERNAL_DISPLAY_CHECK_PASS',
           'scope': 'external text, payload and byte comparisons; not a Lean theorem',
           'checker_sha256': sha256((here / 'check_display.py').read_bytes()).hexdigest(),
           'relocation_checker_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
           'results': results}
(out / 'terminal.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(receipt['status'])
