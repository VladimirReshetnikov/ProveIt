"""Materialize all four actual coefficients, not symbolic stand-ins.

Only imports the newly authored compiler in this same packet. Files are unsigned
little-endian binary integers with no header and minimal byte length.
"""
from pathlib import Path
from hashlib import sha256
import json,gzip
from build_wang943 import layout,audit_geometry,TILES

HERE=Path(__file__).resolve().parent
OUT=HERE/'coefficients';OUT.mkdir(exist_ok=True)
s,E,cp,ce,mu,targets=layout();audit_geometry((s,E,cp,ce,mu,targets))
b,d=s['b'],s['d']

def put(buf,value,bit):
    """OR an exactly known disjoint short field into the bitstream."""
    assert value>=0 and bit>=0
    q,r=divmod(bit,8);value<<=r
    n=(value.bit_length()+7)//8
    chunk=value.to_bytes(n,'little')
    assert q+n<=len(buf)
    for j,v in enumerate(chunk):
        assert not (buf[q+j]&v),'Overlapping nonzero fields'
        buf[q+j]|=v

def ones(n):
    buf=bytearray([255])*((n+7)//8)
    if n%8:buf[-1]=(1<<(n%8))-1
    return buf

def clear(buf,bit):
    q,r=divmod(bit,8)
    assert buf[q]&(1<<r)
    buf[q]&=255^(1<<r)

def emit(name,buf):
    assert buf and buf[-1]
    p=OUT/(name+'.bin');p.write_bytes(buf)
    with gzip.GzipFile(filename='',mode='wb',fileobj=open(OUT/(name+'.bin.gz'),'wb'),mtime=0) as f:f.write(buf)
    value=int.from_bytes(buf,'little')
    return dict(name=name,path='coefficients/'+p.name,encoding='unsigned little-endian, minimal bytes, no header',
                bytes=len(buf),bit_length=value.bit_length(),population=value.bit_count(),
                sha256=sha256(buf).hexdigest(),gzip_bytes=(OUT/(name+'.bin.gz')).stat().st_size,
                gzip_sha256=sha256((OUT/(name+'.bin.gz')).read_bytes()).hexdigest())

records=[]
beta=ones(d);records.append(emit('beta',beta))
mc=bytearray(beta)
for e in E-{1}:clear(mc,b*e)
clear(mc,b*s['e_star']+1)
records.append(emit('MC',mc))
mf=bytearray((d+8)//8)
for t in (s['T1'],s['T2']):put(mf,mu,b*t)
for t,*_ in targets:put(mf,1,b*t)
# Native MF has +4. Source is MF+B-1; subtracting one changes low100 to011.
put(mf,3,0);put(mf,1,d)
records.append(emit('MF_source',mf))
kbits=d+b*s['Hc']+1
kc=bytearray((kbits+7)//8)
for e in s['bare_shifts']:put(kc,1,b*e)
for e,c in ce.items():
    for t in (s['T1'],s['T2']):put(kc,c,b*(t-e))
put(kc,1,d+b*s['Hc'])
records.append(emit('K',kc))

# Independently decode actual on-disk integers and verify exact identities.
actual={r['name']:int.from_bytes((HERE/r['path']).read_bytes(),'little') for r in records}
B=1<<d
assert actual['beta']==B-1
assert actual['MC'].bit_count()==d-989
native=actual['MF_source']-B+1
assert 0<native<B-1 and native%8==4 and native.bit_count()==989
assert 0<actual['MC']<B-1 and actual['MC']%4==2
assert (actual['K']>>d)==1<<(b*s['Hc'])
dc=actual['K']&(B-1)
assert 0<dc<B
assert (2*dc-(1<<(b*s['Hc'])))%5==4
for rec in records:
    assert gzip.decompress((OUT/(rec['name']+'.bin.gz')).read_bytes())==(HERE/rec['path']).read_bytes()
receipt=dict(status='PASS',d=d,B='2^48828125 = 2^(5^11)',
             exact_integers_materialized=True,byte_order='little',files=records,
             total_uncompressed_bytes=sum(r['bytes'] for r in records),
             total_gzip_bytes=sum(r['gzip_bytes'] for r in records),
             actual_integer_population_and_congruence_checks=True)
(HERE/'wang943_materialization_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
