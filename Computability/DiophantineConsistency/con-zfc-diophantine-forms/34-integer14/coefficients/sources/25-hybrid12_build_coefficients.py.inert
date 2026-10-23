#!/usr/bin/env python3
"""Mixed-radix, external-padding Wang943 coefficients; Python standard library.

New layout based on ProveIt wave-3 package 19-wang943.  All integers are
fixed by the literal machine table; this program never runs the machine.
"""
from pathlib import Path
from hashlib import sha256
from itertools import product
import json, gzip

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'k215.tm'
SOURCE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'

def language():
    raw = SOURCE.read_bytes()
    assert sha256(raw).hexdigest() == SOURCE_SHA256
    rows = []
    for line in raw.decode().splitlines():
        if line and not line.startswith('#'):
            q, bit, val, move, target = line.split()
            rows.append((int(q), int(bit), int(val), move, int(target)))
    assert len(rows) == 430
    assert len({(q, bit) for q, bit, *_ in rows}) == 430
    right = sorted({t for q, bit, val, mv, t in rows if mv == 'R'})
    left = sorted({t for q, bit, val, mv, t in rows if mv == 'L'})
    assert (len(right), len(left)) == (199, 45)
    sr = {q: 6+j for j, q in enumerate(right)}
    sl = {q: 205+j for j, q in enumerate(left)}
    head = lambda q, bit: 2*(q+1)+bit
    tiles = []
    tiles += [(0, head(q, bit), sr[t], val) if mv == 'R'
              else (sl[t], head(q, bit), 0, val)
              for q, bit, val, mv, t in rows]
    tiles += [(0, head(215, bit), 0, head(215, bit)) for bit in (0, 1)]
    tiles += [(0, bit, 0, bit) for bit in (0, 1)]
    tiles += [(sr[q], bit, 0, head(q, bit)) for q in right for bit in (0, 1)]
    tiles += [(0, bit, sl[q], head(q, bit)) for q in left for bit in (0, 1)]
    tiles += [(0, c, 0, 438) for c in (0, 1, head(215, 0), head(215, 1))]
    tiles += [(2, 434, 2, 0), (2, 435, 3, 1), (3, 436, 4, head(93, 0)), (4, 436, 4, 0)]
    tiles += [(1, 438, 1, p) for p in (434, 435, 436)]
    tiles += [(l, 437, r, 437) for l in (0, 1, 4) for r in (0, 1, 2)]
    start, forbidden = (2, 435, 3, 1), (5, 0, 0, 0)
    tiles.append(forbidden)
    assert len(tiles) == len(set(tiles)) == 943
    ordered = [start, forbidden] + sorted(set(tiles)-{start, forbidden})
    data = json.dumps(ordered, separators=(',', ':')).encode()+b'\n'
    assert sha256(data).hexdigest() == '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'
    return ordered, data

def construct():
    tiles, tilebytes = language()
    cp = {(t, j): (1023, 1013, 1003, 983)[t]+j
          for t in range(4) for j in range(10)}
    anchors = (1095, 1096, 2195, 3296)
    E = set(range(943)) | set(cp.values()) | {1063,1064} | set(anchors)
    assert len(E) == 989
    weight = lambda j: 1 << (10+2*j)
    ce = {i: 1+sum((((x+512)>>j)&1)*weight(10*t+j)
                    for t, x in enumerate(tile) for j in range(10))
                +sum(weight(j) for j in range(40,44))
          for i, tile in enumerate(tiles)}
    ce.update({e: weight(10*t+j) for (t,j),e in cp.items()})
    ce.update({e: weight(40+j) for j,e in enumerate(anchors)})
    ce.update({1063:0,1064:0})
    mu = 1022 + sum(weight(j) for j in range(44))
    b,L,H,T1,T2 = 125,15625,42,4393,5495
    bare = (30,62,1100,2200)
    targets = [(cp[1,j],{cp[3,j]},set(),{cp[1,j]}) for j in range(10)]
    targets += [(H+cp[0,j],{cp[2,j]},{cp[0,j]},set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    dc = {e:1 for e in bare}
    for e,c in ce.items():
        if c:
            for T in (T1,T2): dc[T-e] = dc.get(T-e,0)+c
    padding = {e:(1<<123)-1 for e in range(9000,9006)}
    padding[9006] = (1<<122)-1
    s = dict(b=b,L=L,d=b*L,H=H,T1=T1,T2=T2,anchors=anchors,bare=bare,
             padding_cells=padding,tile_count=943,support_size=len(E))
    return s,E,cp,ce,mu,targets,dc,padding,tilebytes

def audit(data):
    s,E,cp,ce,mu,targets,dc,padding,tilebytes = data
    H,T1,T2,b,L = (s[n] for n in ('H','T1','T2','b','L'))
    basis_checks = 0
    for t,a,c,y in targets:
        for e in E:
            assert dc.get(t-e,0) == int(e in a)
            assert int(e+H==t) == int(e in c)
            assert int(e==t) == int(e in y)
            basis_checks += 3
    for T in (T1,T2):
        for e in E:
            assert dc.get(T-e,0) == ce[e]
            assert e+H != T
            basis_checks += 2
    Estar = E | {1064}
    assert {(T1-e)%L for e in Estar}.isdisjoint({(T2-e)%L for e in Estar})
    assert {(2195-e)%L for e in E} & {(3296-e)%L for e in E} == {0}
    assert min(dc)>0 and max(dc)+max(E)==8791 < min(padding)
    assert H+max(E) < min(padding)
    assert max(E) < min(padding)
    assert max(padding) < L
    assert len(E) == 2*mu.bit_count()+len(targets)+1+sum(c.bit_count() for c in padding.values()) == 989
    assert mu.bit_length()==97 and mu.bit_count()==53
    assert max(ce.values()).bit_length()==97
    mass=(len(E)+2)*(2*sum(ce.values())+6)
    assert mass.bit_length()==118
    assert (4*mass+8).bit_length()==120
    threshold=max(4*mass+8,2*mu+4,2*max(padding.values())+4,16)
    assert threshold < (1<<b)
    assert (T2-T1)%4==2
    dc5=sum((c%5)*pow(2,e,5) for e,c in dc.items())%5
    unit=(2*dc5-pow(2,H,5))%5
    assert (dc5,unit)==(0,1)
    # Exhaustive local logical checks: selector test, then even copy fields.
    assert [n for n in range(944) if (n & 1022)==0] == [0,1]
    assert [(a,c) for a,c in product((0,1),repeat=2) if ((a+c)&1)==0] == [(0,0),(1,1)]
    return dict(status='PASS',basis_convolution_checks=basis_checks,
        all_rotation_clause_separation=True,anchor_intersection=[0],
        mixed_radix_selector_checks=944,mixed_radix_pair_checks=4,
        clause_mask_population=53,external_padding_population=860,
        native_mask_population=989,mass_bits=118,mass_threshold_bits=120,
        combined_threshold_bits=threshold.bit_length(),radix_exponent=125,
        maximum_canonical_convolution_exponent=8791,first_zero_padding_cell=9000,
        mod5_DC=dc5,mod5_unit=unit)

def emit(data, receipt):
    s,E,cp,ce,mu,targets,dc,padding,tilebytes=data
    b,d,H=(s[n] for n in ('b','d','H'))
    B=1<<d
    DC=sum(c << (b*e) for e,c in dc.items())
    DR=1 << (b*H)
    MC=B-1-sum(1 << (b*e) for e in E-{1})-(2 << (b*1063))
    MF_native=4 + sum(mu << (b*T) for T in (s['T1'],s['T2']))
    MF_native += sum(1 << (b*t) for t,*_ in targets)
    MF_native += sum(c << (b*e) for e,c in padding.items())
    values={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF_native+B-1}
    assert 0<DC<B and 0<MF_native<B-1
    assert MC.bit_count()==d-989 and MF_native.bit_count()==989
    assert MC%4==2 and MF_native%8==4
    assert (2*DC-DR)%5==1
    out=HERE/'coefficients';out.mkdir(exist_ok=True)
    records=[]
    for name,v in values.items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little')
        compressed=gzip.compress(raw,mtime=0)
        (out/(name+'.bin.gz')).write_bytes(compressed)
        assert int.from_bytes(gzip.decompress(compressed),'little')==v
        records.append(dict(name=name,path='coefficients/'+name+'.bin.gz',
            raw_bytes=len(raw),bit_length=v.bit_length(),population=v.bit_count(),
            sha256=sha256(raw).hexdigest(),gzip_bytes=len(compressed),gzip_sha256=sha256(compressed).hexdigest()))
    receipt.update(total_raw_bytes=sum(r['raw_bytes'] for r in records),
                   total_gzip_bytes=sum(r['gzip_bytes'] for r in records),files=records)
    binding=dict(variant='wang943-mixed125-external-padding-5pow9',source_revision=PIN,
      machine_sha256=SOURCE_SHA256,B='2^(5^9)',d=d,rho='2^125',L=15625,
      ports={'Bm1':'beta','Kconstant':'K','MC':'MC','MF':'MF_source'},
      warning='MF means MF_source=MF_native+B-1; replace all four ports together.',
      ordinary_mathematical_proof=True,end_to_end_formal_certificate=False,
      layout=s,audit=receipt)
    (HERE/'COEFFICIENT_BINDING.json').write_text(json.dumps(binding,indent=2)+'\n')
    (HERE/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (HERE/'wang943_tiles.json').write_bytes(tilebytes)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    if not __debug__: raise SystemExit('Do not run with -O')
    data=construct();emit(data,audit(data))
