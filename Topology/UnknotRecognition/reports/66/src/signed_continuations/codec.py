"""Strict, hexadecimal-safe transport for algebraic certificates.

The serialized family is the replay input. No ambient topology or provenance
is authenticated by these routines.
"""
from .core import SignedPartition, Candidate, BasisCertificate


def _hex(value, name):
    if type(value) is not str or not (value.startswith('0x') or value.startswith('-0x')):
        raise ValueError(f'{name} must be a hexadecimal integer string')
    return int(value,16)


def family_to_dict(family):
    return [{"labels":list(c.partition.labels),"offsets":list(c.partition.offsets),
             "cost_hex":hex(c.cost),"token":c.token,"geometry_key":c.geometry_key} for c in family]


def family_from_dict(records):
    if type(records) is not list:
        raise TypeError('family must be a list')
    out=[]
    for r in records:
        if type(r) is not dict or set(r)!={'labels','offsets','cost_hex','token','geometry_key'}:
            raise ValueError('invalid candidate schema')
        if type(r['labels']) is not list or type(r['offsets']) is not list:
            raise ValueError('labels and offsets must be lists')
        out.append(Candidate(SignedPartition(tuple(r['labels']),tuple(r['offsets'])),
                             _hex(r['cost_hex'],'cost'),r['token'],r['geometry_key']))
    return out


def certificate_from_dict(r):
    if type(r) is not dict or set(r)!={'selected','expressions_hex','width','geometry_key'}:
        raise ValueError('invalid certificate schema')
    if type(r['selected']) is not list or type(r['expressions_hex']) is not list:
        raise ValueError('certificate arrays must be lists')
    if type(r['width']) is not int or r['width']<0 or type(r['geometry_key']) is not str:
        raise ValueError('invalid certificate metadata')
    if any(type(i) is not int or i<0 for i in r['selected']):
        raise ValueError('selected indices must be nonnegative integers')
    expressions=tuple(_hex(v,'expression') for v in r['expressions_hex'])
    if any(x<0 for x in expressions):
        raise ValueError('expression masks must be nonnegative')
    return BasisCertificate(tuple(r['selected']),expressions,r['width'],r['geometry_key'])
