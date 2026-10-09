"""Load integration modules against immutable, Git-blob-checked native snapshots."""
from pathlib import Path
import hashlib
import sys
import types

ROOT = Path(__file__).resolve().parents[1]
PINS = {
    'integer_codec.py': 'b88eafacb680e1312df0ecc93170a9f6f53eb639',
    'interval_incidence.py': '3625772c7c20119df64d79a14f644a03e13f7f2f',
    'interval_orbits.py': 'e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8',
    'interval_orbit_verify.py': '0ccb56a0e8b5f1255384121d7417441314727720',
}

def bootstrap():
    for name, expected in PINS.items():
        data = (ROOT / 'snapshots' / 'fastunknot' / name).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual != expected:
            raise RuntimeError(f'Native snapshot Git-blob mismatch: {name}')
    if 'fastunknot' not in sys.modules:
        pkg = types.ModuleType('fastunknot')
        pkg.__path__ = [str(ROOT / 'integration' / 'fastunknot'),
                        str(ROOT / 'snapshots' / 'fastunknot')]
        sys.modules['fastunknot'] = pkg
    return ROOT

if __name__ == '__main__':
    print(bootstrap())
