"""Shared finite input bounds and exclusive output handling for Report243."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import sys
sys.dont_write_bytecode = True
if not hasattr(sys, 'set_int_max_str_digits'):
    raise RuntimeError('Python 3.11 or newer is required')
sys.set_int_max_str_digits(640)
ROOT = Path(__file__).resolve().parents[1]
REPORT_NUMBER = 243
ARTIFACT_STEM = 'Report243'


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
    require(isinstance(value,str), 'output path must be text, not bytes')
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
    env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONINTMAXSTRDIGITS='640', PYTHONHASHSEED='0', PYTHONOPTIMIZE='0')
    return env


def python_command(optimized=None):
    level = sys.flags.optimize if optimized is None else optimized
    integer(level, 0, 2, 'optimization level')
    return [sys.executable, '-B', '-X', 'int_max_str_digits=640'] + (['-' + 'O' * level] if level else [])



def integer_receipt(value):
    """Hash a nonnegative count as minimal big-endian bytes, never huge decimal."""
    require(isinstance(value, int) and not isinstance(value, bool) and value >= 0,
            'receipt value must be a nonnegative integer')
    require(value.bit_length() <= 2_000_000, 'integer receipt bit budget exceeded')
    payload = value.to_bytes(max(1, (value.bit_length() + 7) // 8), 'big')
    out = {'bit_length': value.bit_length(), 'byte_length': len(payload),
           'sha256_unsigned_big_endian': hashlib.sha256(payload).hexdigest()}
    if value.bit_length() <= 1800:
        out['exact_decimal'] = str(value)
    return out
