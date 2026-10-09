"""Portable signed-hex encoding for large certificate integers."""
import json
from pathlib import Path


def _encode(obj):
    if type(obj) is int and obj.bit_length() > 1024:
        return {'$int':format(obj,'x')}
    if isinstance(obj,dict):
        if '$int' in obj:
            raise ValueError("reserved integer-codec key")
        return {k:_encode(v) for k,v in obj.items()}
    if isinstance(obj,(tuple,list)):
        return [_encode(v) for v in obj]
    return obj


def _decode(obj):
    if isinstance(obj,dict):
        if '$int' in obj:
            text=obj['$int']
            if set(obj)!={'$int'} or type(text) is not str or len(text)>250000:
                raise ValueError("invalid or oversized hexadecimal integer")
            digits=text[1:] if text.startswith('-') else text
            if not digits or any(c not in '0123456789abcdef' for c in digits):
                raise ValueError("malformed hexadecimal integer")
            return int(text,16)
        return {k:_decode(v) for k,v in obj.items()}
    if isinstance(obj,list):return [_decode(v) for v in obj]
    return obj


def dumps(obj):
    return json.dumps(_encode(obj),indent=2)+'\n'


def loads(text):
    if len(text)>50_000_000:
        raise ValueError("JSON input exceeds the reference CLI limit")
    return _decode(json.loads(text))


def load(path):
    p=Path(path)
    if p.stat().st_size>50_000_000:
        raise ValueError("JSON input exceeds the reference CLI limit")
    return loads(p.read_text())
