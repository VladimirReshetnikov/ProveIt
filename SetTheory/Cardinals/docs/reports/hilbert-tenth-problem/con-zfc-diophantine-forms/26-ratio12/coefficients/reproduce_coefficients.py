"""Reproduce the parity-separated Wang943 tuple and its finite checks, offline.

Python 3.10+ standard library only. The script writes the four raw binary
integers as well as deterministic compressed versions. No K215 simulation
is used to determine the coefficients.
"""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SCRIPTS = [
    'compiler/build_wang943.py',
    'compiler/build_parity.py',
    'compiler/check_wang_helices.py',
    'compiler/materialize_parity.py',
    'audit/audit_parity_independent.py',
    'audit/audit_parity_cross_agent.py',
]

def load_ports():
    """Return the four actual fixed integers, using the delivered gzip bytes."""
    base = ROOT / 'compiler/coefficients_parity'
    names = ['beta', 'K', 'MC', 'MF_source']
    binding = json.loads((ROOT / 'compiler/COEFFICIENT_BINDING.json').read_text())
    wrapper = json.loads((ROOT / 'COEFFICIENT_BINDING.json').read_text())
    aliases = {'beta':'beta', 'K0':'K', 'MC':'MC', 'MF':'MF_source'}
    assert wrapper['variant'] == binding['variant']
    assert all(binding['circuit_port_aliases'].get(k) == v for k,v in aliases.items())
    assert all(wrapper['circuit_port_aliases'].get(k) == v for k,v in aliases.items())
    records = {row['name']: row for row in binding['files']}
    values = {}
    for name in names:
        raw = gzip.decompress((base / (name + '.bin.gz')).read_bytes())
        assert hashlib.sha256(raw).hexdigest() == records[name]['sha256']
        values[name] = int.from_bytes(raw, 'little')
    return values

def main():
    runs = []
    for script in SCRIPTS:
        run = subprocess.run([sys.executable, '-B', str(ROOT / script)],
                             cwd=ROOT, capture_output=True, text=True)
        if run.returncode:
            sys.stdout.write(run.stdout)
            sys.stderr.write(run.stderr)
            raise SystemExit(run.returncode)
        runs.append({'script': script, 'exit_code': run.returncode})
    values = load_ports()
    beta, K, MC, MFsrc = [values[x] for x in ['beta', 'K', 'MC', 'MF_source']]
    B = beta + 1
    d = 5**10
    assert B == 1 << d
    MF = MFsrc - beta
    # B is a power of two: avoid quadratic long division on million-bit data.
    DC, DR = K & beta, K >> d
    assert 0 < MC < beta and 0 < MF < beta
    assert MC % 4 == 2 and MF % 8 == 4
    assert MC.bit_count() + MF.bit_count() == d
    assert MF.bit_count() == 989
    assert (2*DC-DR) % 5 == 3
    assert DR == 1 << 625
    receipt = {
        'status': 'PASS', 'runs': runs,
        'd': d, 'native_high_population': MF.bit_count(),
        'native_low_population': MC.bit_count(),
        'mod5_unit': (2*DC-DR) % 5,
        'all_four_frozen_raw_hashes_match': True,
        'scope': 'New parity coefficient replay; universal compiler and K215 equivalence remain mathematical dependencies.'
    }
    (ROOT / 'COEFFICIENT_REPLAY.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
