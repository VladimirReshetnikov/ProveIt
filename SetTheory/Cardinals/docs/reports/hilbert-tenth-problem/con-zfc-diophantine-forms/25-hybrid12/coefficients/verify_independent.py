#!/usr/bin/env python3
"""Read-only independent checks; does not import or execute the builder.

Checks the materialized tuple against a separate finite reconstruction and
tests every tile's clause code and every single copy/anchor mutation.
"""
from pathlib import Path
from hashlib import sha256
import gzip,json

ROOT=Path(__file__).resolve().parent

def main():
    if not __debug__:raise SystemExit('Do not run with -O')
    manifest=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
    tiles=json.loads((ROOT/'wang943_tiles.json').read_text())
    assert len(tiles)==943
    assert sha256((ROOT/'wang943_tiles.json').read_bytes()).hexdigest()=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'
    values={}
    for rec in manifest['audit']['files']:
        packed=(ROOT/rec['path']).read_bytes()
        raw=gzip.decompress(packed)
        assert sha256(packed).hexdigest()==rec['gzip_sha256']
        assert sha256(raw).hexdigest()==rec['sha256']
        v=int.from_bytes(raw,'little')
        assert v.bit_length()==rec['bit_length'] and v.bit_count()==rec['population']
        values[rec['name']]=v
    d=1953125;B=2**d;rho=2**125
    beta,K,MC,MFs=(values[k] for k in ('beta','K','MC','MF_source'))
    DC,DR=K%B,K//B;MF=MFs-B+1
    assert beta==B-1 and DR==2**5250
    assert (MC.bit_count(),MF.bit_count())==(1952136,989)
    assert 0<DC<B and 0<MC<B-1 and 0<MF<B-1
    assert (MC%4,MF%8,(2*DC-DR)%5)==(2,4,1)
    native=set(range(943))|set(range(983,993))|set(range(1003,1033))|{1063,1064,1095,1096,2195,3296}
    assert len(native)==989
    assert MC==B-1-sum(1<<(125*e) for e in native if e!=1)-(2<<(125*1063))
    copies=[list(range(o,o+10)) for o in (1023,1013,1003,983)]
    fields=[2**(10+2*j) for j in range(44)]
    coeff={}
    valid_masks=[]
    for i,tile in enumerate(tiles):
        bits=[((label+512)>>j)&1 for label in tile for j in range(10)]+[1]*4
        coeff[i]=1+sum(v*w for v,w in zip(bits,fields))
        valid_masks.append(bits)
    for slot in range(4):
        for j in range(10):coeff[copies[slot][j]]=fields[slot*10+j]
    for e,w in zip((1095,1096,2195,3296),fields[40:]):coeff[e]=w
    coeff[1063]=coeff[1064]=0
    assert set(coeff)==native
    expected_dc={30:1,62:1,1100:1,2200:1}
    for e,c in coeff.items():
        for T in (4393,5495):expected_dc[T-e]=expected_dc.get(T-e,0)+c
    expected_dc={e:c for e,c in expected_dc.items() if c}
    # Slice actual bytes instead of trusting any builder-side sparse object.
    raw=DC.to_bytes((d+7)//8,'little')
    seen={}
    for e in range(15625):
        byte,shift=divmod(125*e,8)
        c=(int.from_bytes(raw[byte:byte+17],'little')>>shift)&(rho-1)
        if c:seen[e]=c
    assert seen==expected_dc
    mu=1022+sum(fields)
    base_targets=set(range(1013,1023))|set(range(1065,1075))|{2195,3296}
    pad=sum(((2**123-1) if e<9006 else (2**122-1))<<(125*e) for e in range(9000,9007))
    expected_mf=4+sum(mu<<(125*T) for T in (4393,5495))+sum(1<<(125*t) for t in base_targets)+pad
    assert MF==expected_mf
    assert [n for n in range(944) if not n&1022]==[0,1]
    mutation_checks=0
    for i,bits in enumerate(valid_masks):
        S=coeff[i]+sum(v*w for v,w in zip(bits,fields))
        assert S&mu==0
        for j in range(44):
            changed=S+(1-2*bits[j])*fields[j]
            assert changed&mu
            mutation_checks+=1
    assert mu&0==0
    for w in fields:assert mu&w
    # Exact convolution target identities, evaluated from actual DC digits.
    expected=[]
    for j in range(10):expected.append((1013+j,{983+j},set(),{1013+j}))
    for j in range(10):expected.append((1065+j,{1003+j},{1023+j},set()))
    expected.extend([(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})])
    checks=0
    for t,a,b,c in expected:
        for e in native:
            assert seen.get(t-e,0)==int(e in a)
            assert int(e+42==t)==int(e in b)
            assert int(e==t)==int(e in c)
            checks+=3
    for t in (4393,5495):
        for e in native:
            assert seen.get(t-e,0)==coeff[e]
            assert e+42!=t
            checks+=2
    assert {(4393-e)%15625 for e in native}.isdisjoint({(5495-e)%15625 for e in native})
    assert {(2195-e)%15625 for e in native}&{(3296-e)%15625 for e in native}=={0}
    # All output native exponent supports avoid the complete padding region.
    output_support={r+e for r in seen for e in native}|{42+e for e in native}|native
    assert max(output_support)==8791 and not output_support&set(range(9000,9007))
    receipt={'status':'PASS','builder_imported':False,'materialized_ports_checked':4,
      'native_convolution_identities':checks,'valid_tile_clauses':943,
      'single_copy_anchor_mutations_rejected':mutation_checks,
      'empty_copy_anchor_mutations_rejected':44,'selector_counts_checked':944,
      'padding_native_support_disjoint':True,'max_native_output_exponent':8791,
      'actual_byte_hashes_checked':4,'all_rotation_support_intersections_checked':True}
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
