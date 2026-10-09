"""Exact portable hexadecimal integer transport; no decimal-limit mutation."""
import json


def pack(value):
    if type(value) is int:
        return {'$integer':hex(value)}
    if isinstance(value, (list, tuple)):
        return [pack(x) for x in value]
    if isinstance(value, dict):
        if any(not isinstance(k,str) for k in value):
            raise ValueError('transport dictionary keys must be strings')
        return {k:pack(v) for k,v in value.items()}
    if value is None or isinstance(value, (str,bool)):
        return value
    raise ValueError('unsupported transport value')


def unpack(value):
    if isinstance(value, list):
        return [unpack(x) for x in value]
    if isinstance(value, dict):
        if set(value) == {'$integer'}:
            token = value['$integer']
            if not isinstance(token,str):
                raise ValueError('invalid encoded integer')
            parsed = int(token,16)
            if hex(parsed) != token:
                raise ValueError('noncanonical encoded integer')
            return parsed
        return {k:unpack(v) for k,v in value.items()}
    return value


def dumps(value):
    return json.dumps(pack(value), sort_keys=True, indent=2)


def loads(text):
    return unpack(json.loads(text))
