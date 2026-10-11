"""Independent replay of an integral vertex coboundary on one actual source."""
from hashlib import sha256
import json

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare,NormalOrbitError
from .cocycle_transport_verify import _read_heights,_check_signed_edges,_shield_callback


@_shield_callback
def verify_cocycle_gauge(triangulation,heights,certificate,*,check=lambda:None):
    check()
    if (type(certificate)is not dict or set(certificate)!={'schema','source_sha256','potential','heights'}
            or certificate['schema']!='cocycle-vertex-gauge-v1'):return False
    digest=sha256(json.dumps(triangulation,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    if certificate['source_sha256']!=digest:return False
    try:
        prepared=_prepare(triangulation,check);n=len(prepared['tetrahedra'])
        before=_read_heights(heights,n,check);after=_read_heights(certificate['heights'],n,check)
        if before is None or after is None or not _check_signed_edges(prepared,before,check):return False
        pairs=certificate['potential']
        if type(pairs)is not list:return False
        roots=sorted(set(prepared['vertex_roots']));potential={}
        if len(pairs)!=len(roots):return False
        for expected,item in zip(roots,pairs):
            check()
            if type(item)is not list or len(item)!=2 or type(item[0])is not int or item[0]!=expected:return False
            potential[expected]=encoded_integer(item[1])
        for t,row in enumerate(before):
            check();shifted=[row[j]+potential[prepared['vertex_roots'][4*t+j]]for j in range(4)]
            expected=[value-shifted[0]for value in shifted]
            if after[t]!=expected:return False
        return _check_signed_edges(prepared,after,check)
    except (NormalOrbitError,ValueError,TypeError,KeyError,IndexError):return False
