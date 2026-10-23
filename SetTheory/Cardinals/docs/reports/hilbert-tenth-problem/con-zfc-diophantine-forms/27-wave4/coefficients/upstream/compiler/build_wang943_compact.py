"""Tighter exact-support layout, preserving the earlier 5^11 fallback.

Imports only the newly authored Wang language/bit compiler in this packet.
All finite collision checks here concern the actual support, not estimates.
"""
from pathlib import Path
from hashlib import sha256
import json
from build_wang943 import layout as fallback_layout,TILES

HERE=Path(__file__).resolve().parent

def layout():
    s,E,cp,ce,mu,_=fallback_layout()
    old=tuple(s['anchors']); new=(1095,1096,2195,3296)
    E=E-set(old)|set(new)
    weights=[ce.pop(e) for e in old]
    ce.update(dict(zip(new,weights)))
    s.update(anchors=new,Emax=3296,Hc=5497,T1=7631,T2=8733,
             gap=1102,L=15625,d=5**10,bare_shifts=(30,5517,1100,2200))
    # M was only a fallback layout parameter; no single-ruler multiplier here.
    s.pop('M')
    targets=[(cp[1,j],{cp[3,j]},set(),{cp[1,j]}) for j in range(10)]
    targets += [(5497+cp[0,j],{cp[2,j]},{cp[0,j]},set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    return s,E,cp,ce,mu,targets

def audit_geometry(data):
    s,E,cp,ce,mu,targets=data
    T1,T2,H,L=s['T1'],s['T2'],s['Hc'],s['L']
    # Sparse full DC polynomial coefficients, including both clause bands.
    dc={x:1 for x in s['bare_shifts']}
    for e,c in ce.items():
        for t in (T1,T2):dc[t-e]=dc.get(t-e,0)+c
    checks=0
    for target,at0,at1,at2 in targets:
        for e in E:
            assert dc.get(target-e,0)==int(e in at0),(target,e,'DC')
            assert int(e+H==target)==int(e in at1),(target,e,'DR')
            assert int(e==target)==int(e in at2),(target,e,'Y')
            checks+=3
    for t in (T1,T2):
        for e in E:
            assert dc.get(t-e,0)==ce[e],(t,e,'clause')
            assert e+H!=t,(t,e,'clause DR')
            checks+=2
    Estar=E|{s['e_star']+1}
    assert {(T1-e)%L for e in Estar}.isdisjoint({(T2-e)%L for e in Estar})
    assert {(2195-e)%L for e in E}&{(3296-e)%L for e in E}=={0}
    assert min(dc)>0 and max(dc)+max(E)<L
    assert H+max(E)<L and T1>max(E) and T2>max(E)
    assert max(target for target,*_ in targets)<L
    assert T2-T1 not in {x-y for x in Estar for y in Estar}
    assert (T2-T1)%4==2
    dc5=sum((c%5)*pow(2,e,5) for e,c in dc.items())%5
    assert (2*dc5-pow(2,H,5))%5==4
    assert len(E)==2*mu.bit_count()+len(targets)+1==989
    assert s['b']==625 and L==15625 and s['d']==5**10
    return dict(status='PASS',basis_convolution_checks=checks,
                all_rotation_clause_hit_sets_disjoint=True,
                all_rotation_anchor_intersection=[0],
                exact_clause_band_gap_outside_support_difference_set=True,
                max_unshifted_degree=max(dc)+max(E),cell_length=L,
                mod5_unit=4,mask_population=989)

def output():
    data=layout(); audit=audit_geometry(data); s=data[0]
    receipt=dict(status='PASS',variant='wang943-compact-5pow10',layout=s,audit=audit,
                 tile_sha256=sha256((HERE/'wang943_tiles.json').read_bytes()).hexdigest(),
                 proof='WANG943_COMPACT_LAYOUT.md')
    (HERE/'wang943_compact_layout.json').write_text(json.dumps(s,indent=2)+'\n')
    (HERE/'wang943_compact_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':output()

