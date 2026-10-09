"""Load the two separately pinned upstream modules; verify their Git identities."""
from functools import lru_cache
from hashlib import sha1
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import sys

PINS = {
    'interval_orbits': 'e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8',
    'interval_orbit_verify': '0ccb56a0e8b5f1255384121d7417441314727720',
}

@lru_cache(maxsize=2)
def load_kernel(name):
    if name not in PINS:
        raise ValueError('unknown pinned kernel')
    path = Path(__file__).resolve().parents[2] / 'vendor' / (name + '.py')
    source = path.read_bytes()
    blob = sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest()
    if blob != PINS[name]:
        raise RuntimeError('vendored kernel differs from its recorded Git blob: ' + name)
    module_name = '_sparse_incidence_vendor_' + name
    spec = spec_from_file_location(module_name, path)
    module = module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module
