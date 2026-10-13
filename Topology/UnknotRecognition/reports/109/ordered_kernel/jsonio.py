"""Interchange with explicit binary-large integer tags; no global digit-limit changes."""
import json

def _pack(x):
    if type(x) is int and x.bit_length()>256:
        return {'$integer_hex': hex(x)}
    if isinstance(x,dict):
        return {str(k):_pack(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [_pack(v) for v in x]
    return x

def _unpack(x):
    if isinstance(x,dict):
        if set(x)=={'$integer_hex'}:
            value=x['$integer_hex']
            if type(value) is not str or not (value.startswith('0x') or value.startswith('-0x')):
                raise ValueError('invalid large-integer tag')
            return int(value,16)
        return {k:_unpack(v) for k,v in x.items()}
    if isinstance(x,list):return [_unpack(v) for v in x]
    return x

def dumps(obj):
    return json.dumps(_pack(obj),indent=2,sort_keys=True)+'\n'

def loads(text):
    def unique(pairs):
        d={}
        for k,v in pairs:
            if k in d: raise ValueError('duplicate JSON key')
            d[k]=v
        return d
    return _unpack(json.loads(text,object_pairs_hook=unique))

def parse_input(obj):
    if type(obj) is not dict or obj.get('schema')!='occurrence-matrix-v1' or type(obj.get('rows')) is not list:
        raise ValueError('expected occurrence-matrix-v1 with a rows list')
    counts={};weights={}
    for row in obj['rows']:
        if type(row) is not dict or type(row.get('id')) is not int or row['id'] in counts:
            raise ValueError('invalid or duplicate row id')
        if type(row.get('entries')) is not list:
            raise ValueError('row entries must be pairs')
        values={}
        for pair in row['entries']:
            if type(pair) is not list or len(pair)!=2 or type(pair[0]) is not int or pair[0] in values:
                raise ValueError('invalid or duplicate column entry')
            values[pair[0]]=pair[1]
        counts[row['id']]=values;weights[row['id']]=row.get('weight',1)
    from .model import Matrix
    Matrix.parse(counts,weights)
    return counts,weights
