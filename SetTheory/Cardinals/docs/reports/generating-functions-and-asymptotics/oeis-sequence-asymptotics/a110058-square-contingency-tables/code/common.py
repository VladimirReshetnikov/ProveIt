"""Shared finite input bounds and exclusive output handling for Report236."""
from __future__ import annotations
import json
import os
from pathlib import Path
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_STEM = 'Report236'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, lower, upper, label):
    require(isinstance(value, int) and not isinstance(value, bool), label + ' must be an integer')
    require(lower <= value <= upper, '%s must be in [%d, %d]' % (label, lower, upper))
    return value


def new_file_path(value):
    """Validate before normalization; outputs may never replace sources or files.

    The caller must still open with x/xb or mkdir(exist_ok=False). These are
    finite filesystem guards, not a sandbox against concurrent hostile changes.
    """
    require(isinstance(value, (str, os.PathLike)) and bool(str(value)), 'output path must be nonempty')
    value = os.fspath(value)
    require('\\' not in value, 'backslash output components are forbidden')
    require(not any(part in ('.', '..') for part in value.split(os.sep)),
            'output path must not contain dot or dot-dot components')
    out = Path(os.path.abspath(value))
    for path in (out, *out.parents):
        require(not path.is_symlink(), 'output path has a live or dangling symlink ancestor')
    require(not out.exists(), 'output path must be new')
    require(out != ROOT and ROOT not in out.parents, 'output must be outside the source package')
    require(out.parent.is_dir(), 'output parent must already exist')
    return out


def emit(data, output=None):
    encoded = json.dumps(data, indent=2, sort_keys=True, ensure_ascii=True) + '\n'
    if output is None:
        print(encoded, end='')
    else:
        path = new_file_path(output)
        with path.open('x', encoding='utf-8', newline='\n') as handle:
            handle.write(encoded)


def child_environment():
    env = os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONINTMAXSTRDIGITS='640', PYTHONHASHSEED='0')
    return env


def python_command(optimized=None):
    level = sys.flags.optimize if optimized is None else optimized
    integer(level, 0, 2, 'optimization level')
    return [sys.executable, '-B'] + (['-' + 'O' * level] if level else [])


def degree_specification(values, even=True, allow_empty=False):
    """The supported finite domain: degrees 3..8, at most six vertices,
    total degree at most 18 and sum(degree-2) at most six.
    Internal moment sublists may be empty or have odd total degree.
    """
    require(isinstance(values, (list, tuple)), 'degrees must be a list or tuple')
    require((0 if allow_empty else 1) <= len(values) <= 6, 'vertex cutoff')
    ds = tuple(integer(d, 3, 8, 'degree') for d in values)
    require(sum(ds) <= 18, 'total-degree cutoff')
    require(sum(d-2 for d in ds) <= 6, 'diagram-cost cutoff')
    require(not even or sum(ds) % 2 == 0, 'total degree must be even')
    return tuple(sorted(ds))


def expected_specifications():
    """Fixed independent fixture list; order is the article's cost order."""
    return ((3,3),(4,),(3,3,3,3),(3,3,4),(3,5),(4,4),(6,),
            (3,3,3,3,3,3),(3,3,3,3,4),(3,3,3,5),(3,3,4,4),(3,3,6),
            (3,4,5),(3,7),(4,4,4),(4,6),(5,5),(8,))


def validated_wick_receipt():
    path = ROOT / 'code/connected_wick_receipt.json'
    require(path.is_file() and not path.is_symlink(), 'missing regular coefficient receipt')
    require(path.stat().st_size <= 64000, 'coefficient receipt size cutoff')
    data = json.loads(path.read_text(encoding='utf-8'))
    require(isinstance(data, dict) and isinstance(data.get('rows'), list), 'invalid coefficient receipt')
    require(len(data['rows']) == 18, 'coefficient receipt must contain exactly 18 rows')
    observed = []
    for row in data['rows']:
        require(isinstance(row, dict), 'invalid coefficient row')
        ds = degree_specification(row.get('degrees'))
        observed.append(ds)
        poly = row.get('cumulant')
        require(isinstance(poly, dict) and 1 <= len(poly) <= 7, 'invalid Laurent polynomial')
        for exponent, value in poly.items():
            require(isinstance(exponent, str) and exponent in tuple(str(i) for i in range(-6, 1)), 'invalid Laurent exponent')
            require(isinstance(value, str) and 1 <= len(value) <= 128, 'invalid rational value')
    require(tuple(observed) == expected_specifications(), 'coefficient specifications differ from fixed domain')
    return data
