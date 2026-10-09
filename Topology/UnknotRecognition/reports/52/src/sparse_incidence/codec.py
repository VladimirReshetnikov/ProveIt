"""Exact, portable JSON transport without changing interpreter limits."""
import json
import re
from pathlib import Path

_HEX = re.compile(r'[+-]?0[xX][0-9a-fA-F]+\Z')

def encode(value):
    if type(value) is int:
        return hex(value) if value.bit_length() > 4096 else value
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value

def decode(value):
    if isinstance(value, str) and _HEX.fullmatch(value):
        return int(value, 16)
    if isinstance(value, dict):
        return {k: decode(v) for k, v in value.items()}
    if isinstance(value, list):
        return [decode(v) for v in value]
    return value

def dumps(value, **kwargs):
    return json.dumps(encode(value), **kwargs)

def load(path):
    return decode(json.loads(Path(path).read_text(encoding='utf-8')))

def save(path, value):
    Path(path).write_text(dumps(value, indent=2, sort_keys=True) + '\n', encoding='utf-8')
