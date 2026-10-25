"""Authentication, canonical JSON and external I/O only; no polynomial algebra."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BASE = REPO / 'Computability/DiophantineConsistency'
SOURCE = BASE / 'research/balanced-crt-gate-shear-verification/data'
DATA = Path('/tmp/proveit-neighbor-gate-shear-data-v1')
CORE = {'README.md', 'PROOF.md', 'TOOLCHAIN.md', 'guard.py', 'build.py',
        'check.py', 'SOURCE_PINS.json'}
PROFILE_FILES = ('equation.json', 'expanded_polynomial.json',
                 'shear_certificate.json', 'METRICS.json',
                 'COMPOSED_MAPS.json', 'ENDPOINT_BINDING.json')
ARTIFACTS = {f'{p}/{f}' for p in ('plain', 'weighted') for f in PROFILE_FILES}
ARTIFACTS.add('INDEX.json')


def need(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'),
                       allow_nan=False) + '\n').encode()


def equal(left, right):
    return encode(left) == encode(right)


def record_bytes(value):
    return {'bytes': len(value), 'sha256': hashlib.sha256(value).hexdigest()}


def record(path):
    return record_bytes(Path(path).read_bytes())


def obj(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique,
                      parse_constant=lambda _: (_ for _ in ()).throw(
                          ValueError('nonfinite JSON number')))


def plain_path(path):
    path = Path(path)
    need(path.is_absolute() and '..' not in path.parts, 'absolute plain path')
    need(not path.is_relative_to(REPO), 'output inside repository')
    for part in (path, *path.parents):
        need(not part.is_symlink(), 'symlink path component')
    return path


def external_data(path, *, absent):
    path = plain_path(path)
    need(path == DATA, 'unreviewed data path')
    need(not path.exists() if absent else path.is_dir(), 'data freshness/type')
    return path


def external_receipt(path, role):
    path = plain_path(path)
    need(role in {'build', 'check', 'check-optimized', 'rebuild',
                  'rebuild-optimized'}, 'receipt role')
    allowed = {Path('/tmp/neighbor-gate-shear-' + role + '.json')}
    if role != 'build':
        allowed.add(Path('/tmp/neighbor-gate-shear-root-' + role + '.json'))
    need(path in allowed, 'unreviewed receipt path')
    need(not path.exists() and path.parent.is_dir(), 'receipt freshness')
    return path


def file_members(folder):
    need(folder.is_dir() and not folder.is_symlink(), 'input folder type')
    result = set()
    for path in folder.rglob('*'):
        need(not path.is_symlink(), 'symlink input member')
        need(path.is_file() or path.is_dir(), 'nonregular input member')
        if path.is_file():
            result.add(str(path.relative_to(folder)))
    return result


def check_record(path, expected):
    need(set(expected) == {'bytes', 'sha256'} and
         type(expected['bytes']) is int and expected['bytes'] >= 0 and
         type(expected['sha256']) is str and len(expected['sha256']) == 64,
         'record schema/type')
    need(not path.is_symlink() and path.is_file(), 'input file type')
    need(equal(record(path), expected), 'input bytes/hash: ' + str(path))


def authenticate():
    hold = obj(HERE / 'HOLD_INVENTORY.json')
    need(hold['schema'] == 'held_neighbor_gate_shear_finite_v1', 'HOLD schema')
    need(set(hold['files']) == CORE and
         file_members(HERE) == CORE | {'HOLD_INVENTORY.json'}, 'held closure')
    for name, expected in hold['files'].items():
        check_record(HERE / name, expected)
    pins = obj(HERE / 'SOURCE_PINS.json')
    need(pins['schema'] == 'held_neighbor_gate_shear_finite_pins_v1', 'pins schema')
    need(set(pins['own_core']) == CORE - {'SOURCE_PINS.json'}, 'own core closure')
    for name, expected in pins['own_core'].items():
        check_record(HERE / name, expected)
    for name, expected in pins['external_files'].items():
        relative = Path(name)
        need(not relative.is_absolute() and '..' not in relative.parts,
             'external pin path')
        check_record(BASE / relative, expected)
    for folder, members in pins['whole_trees'].items():
        root = BASE / folder
        need(file_members(root) == set(members), 'whole input closure: ' + folder)
        for name, expected in members.items():
            need(equal(pins['external_files'][folder + '/' + name], expected),
                 'whole input flattening')
    need(not (BASE / 'research/round16-common-name-centering/MANIFEST.json').exists(),
         'observed source relabeled')
    return pins


def source(profile, name):
    return obj(SOURCE / profile / name)


def source_record(profile, name):
    return record(SOURCE / profile / name)


def bundle_records(bundle):
    return {name: record_bytes(encode(value)) for name, value in sorted(bundle.items())}


def read_bundle(folder):
    need(file_members(folder) == ARTIFACTS, 'data inventory members')
    bundle = {}
    for name in sorted(ARTIFACTS):
        raw = (folder / name).read_bytes()
        value = obj(folder / name)
        need(encode(value) == raw, 'canonical JSON bytes')
        bundle[name] = value
    return bundle


def save_bundle(folder, bundle):
    need(set(bundle) == ARTIFACTS, 'producer data inventory')
    folder.mkdir()
    for name, value in sorted(bundle.items()):
        path = folder / name
        path.parent.mkdir(exist_ok=True)
        plain_path(path)
        with path.open('xb') as stream:
            stream.write(encode(value))


def report(path, value):
    plain_path(path)
    raw = (json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + '\n').encode()
    with path.open('xb') as stream:
        stream.write(raw)
    import sys
    sys.stdout.buffer.write(raw)
