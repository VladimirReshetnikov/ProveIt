"""Shared finite input bounds and exclusive output handling for Report235."""
from __future__ import annotations
import json
import os
from pathlib import Path
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
ROOT = Path(__file__).resolve().parents[1]


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
    level = sys.flags.optimize if optimized is None else int(optimized)
    integer(level, 0, 2, 'optimization level')
    return [sys.executable, '-B'] + (['-' + 'O' * level] if level else [])
