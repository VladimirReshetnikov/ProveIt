"""Strict input and inventory support. All guards survive Python optimization."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import re

MAX_BYTES = 262144
MAX_FILES = 32
REQUIRED_FILES={"support.py","exact_math.py","interval_math.py","run_checks.py","mutation_tests.py","fixtures.json","README.md"}

class CheckFailure(Exception):
    def __init__(self, name, detail=''):
        self.name, self.detail = name, str(detail)
        super().__init__(name + ': ' + str(detail))

def need(test, name, detail=''):
    if not test:
        raise CheckFailure(name, detail)

def exact_json(path, name):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, name, 'duplicate key ' + key)
            out[key] = value
        return out
    def integer(s):
        need(len(s) <= 100, name, 'integer exceeds 100 characters')
        return int(s)
    def reject(s):
        raise CheckFailure(name, 'noninteger JSON number: ' + s)
    try:
        need(path.is_file() and not path.is_symlink(), name, 'not an ordinary file')
        need(path.stat().st_size <= MAX_BYTES, name, 'file too large')
        return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=pairs,
                          parse_int=integer, parse_float=reject, parse_constant=reject)
    except (OSError, ValueError, UnicodeError) as error:
        raise CheckFailure(name, error) from None

def keys(value, names, diagnostic):
    need(type(value) is dict and set(value) == set(names), diagnostic)

def inventory(root):
    files = {}
    need(root.is_dir() and not root.is_symlink(), 'INTEGRITY_ROOT')
    entries = list(root.rglob('*'))
    need(len(entries) <= 64, 'INTEGRITY_COUNT')
    for path in sorted(entries):
        name = path.relative_to(root).as_posix()
        need(not path.is_symlink(), 'INTEGRITY_SYMLINK', name)
        need(path.is_dir() or path.is_file(), 'INTEGRITY_SPECIAL_FILE', name)
        need(not path.is_dir(), 'INTEGRITY_UNLISTED_DIRECTORY', name)
        if path.is_file():
            need(path.stat().st_size <= MAX_BYTES, 'INTEGRITY_SIZE', name)
            files[name] = sha256(path.read_bytes()).hexdigest()
    need(len(files) <= MAX_FILES, 'INTEGRITY_COUNT')
    return files

def integrity(root):
    actual = inventory(root)
    need('MANIFEST.json' in actual, 'INTEGRITY_MISSING', 'MANIFEST.json')
    manifest = exact_json(root/'MANIFEST.json', 'INTEGRITY_MANIFEST')
    keys(manifest, ['format', 'files'], 'INTEGRITY_MANIFEST')
    need(type(manifest['format']) is int and manifest['format'] == 1, 'INTEGRITY_MANIFEST')
    need(type(manifest['files']) is dict and 0 < len(manifest['files']) <= MAX_FILES,
         'INTEGRITY_MANIFEST')
    expected = manifest['files']
    need(set(expected)==REQUIRED_FILES,'INTEGRITY_MANIFEST_FILES')
    for name, digest in expected.items():
        need(type(name) is str and re.fullmatch(r'[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*', name)
             and all(part not in ('.','..') for part in name.split('/')) and name != 'MANIFEST.json'
             and type(digest) is str and re.fullmatch(r'[0-9a-f]{64}', digest), 'INTEGRITY_MANIFEST')
        need(name in actual, 'INTEGRITY_MISSING', name)
        need(actual[name] == digest, 'INTEGRITY_HASH', name)
    actual.pop('MANIFEST.json')
    need(set(actual) == set(expected), 'INTEGRITY_UNLISTED', sorted(set(actual)-set(expected)))
    return len(actual)

def rational(value, diagnostic):
    need(type(value) is str and len(value) <= 1024 and
         re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value), diagnostic)
    result = F(value)
    need(str(result) == value, diagnostic, 'not canonical')
    return result

def decimal(value, places, diagnostic):
    need(type(value) is str and len(value) < 128 and
         re.fullmatch(r'-?(?:0|[1-9][0-9]*)\.[0-9]{'+str(places)+'}', value), diagnostic)
    return F(value)

def interval(value, places, diagnostic):
    keys(value, ['lower','upper'], diagnostic)
    lo, hi = (decimal(value[k], places, diagnostic) for k in ('lower','upper'))
    need(lo < hi, diagnostic)
    return lo, hi

