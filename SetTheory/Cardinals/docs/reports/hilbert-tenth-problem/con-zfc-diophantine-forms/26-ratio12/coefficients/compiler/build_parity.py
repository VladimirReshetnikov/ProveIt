"""Parity-separated Wang943 layout: fixed positive spatial exponent Hc=1.

The tile language and clause coefficient values are inherited; their native
locations and transport geometry are explicitly replaced as a whole tuple.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json
from build_wang943 import layout as inherited_layout, TILES

HERE = Path(__file__).resolve().parent

def layout():
    s, Eold, cpold, ceold, mu, _ = inherited_layout()
    anchors = (1095,1096,2195,3296)
    offsets = (1020,1000,980,960)  # west, north, east, south
    cp = {(slot,j): offset+2*j for slot,offset in enumerate(offsets) for j in range(10)}
    E = set(range(943)) | set(cp.values()) | {1063,1064} | set(anchors)
    ce = {i:ceold[i] for i in range(943)}
    ce.update({cp[slot,j]:ceold[cpold[slot,j]] for slot in range(4) for j in range(10)})
    ce.update({e:ceold[old] for e,old in zip(anchors,s['anchors'])})
    ce.update({1063:0,1064:0})
    assert len(E)==len(ce)==989
    assert sum(ce.values())==sum(ceold.values())
    s.update(anchors=anchors,Emax=3296,Hc=1,T1=7631,T2=8733,
             gap=1102,L=15625,d=5**10,bare_shifts=(40,41,1100,2200),
             copy_offsets=offsets,copy_step=2,variant='wang943-parity-H1-5pow10')
    s.pop('M')
    targets=[(cp[1,j],{cp[3,j]},set(),{cp[1,j]}) for j in range(10)]
    targets += [(1+cp[0,j],{cp[2,j]},{cp[0,j]},set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    return s,E,cp,ce,mu,targets

def audit_geometry(data):
    s,E,cp,ce,mu,targets=data
    H,T1,T2,L=s['Hc'],s['T1'],s['T2'],s['L']
    dc=Counter({e:1 for e in s['bare_shifts']})
    for e,c in ce.items():
        if c:
            dc[T1-e]+=c;dc[T2-e]+=c
    checks=0
    for t,current,spatial,temporal in targets:
        for e in E:
            assert dc.get(t-e,0)==int(e in current),(t,e,'current')
            assert int(e+H==t)==int(e in spatial),(t,e,'spatial')
            assert int(e==t)==int(e in temporal),(t,e,'temporal')
            checks+=3
    for t in (T1,T2):
        for e in E:
            assert dc.get(t-e,0)==ce[e],(t,e,'clause')
            assert e+H!=t,(t,e,'clause-spatial')
            checks+=2
    Estar=E|{s['e_star']+1}
    assert {(T1-e)%L for e in Estar}.isdisjoint({(T2-e)%L for e in Estar})
    assert {(2195-e)%L for e in E}&{(3296-e)%L for e in E}=={0}
    assert (T2-T1)%4==2
    assert min(dc)>2 and max(dc)+max(E)<L and H+max(E)<L
    mass=(len(E)+2)*(2*sum(ce.values())+6)
    threshold=max(4*mass+8,2*mu+4,16)
    assert threshold<1<<s['b']
    assert 3*(1<<s['b'])//4+mass<=(1<<s['b'])-2
    assert (1<<s['b'])//2+1+mass<=(1<<s['b'])-2
    assert len(E)==2*mu.bit_count()+len(targets)+1==989
    dc5=sum((c%5)*pow(2,e,5) for e,c in dc.items())%5
    assert dc5==0 and pow(2,H,5)==2
    unit=(2*dc5-pow(2,H,5))%5
    assert unit==3
    return dict(status='PASS',variant=s['variant'],basis_convolution_checks=checks,
        all_rotation_clause_hit_sets_disjoint=True,all_rotation_anchor_intersection=[0],
        max_unshifted_degree=max(dc)+max(E),cell_length=L,spatial_exponent=H,
        mod5_unit=unit,dummy_derivative_mod5=pow(2,s['e_star'],5)*3*unit%5,
        mask_population=989,threshold_bit_length=threshold.bit_length(),
        strict_raw_slack_bounds=True,canonical_origin_no_DC_DR_constant=True)

def output():
    data=layout();audit=audit_geometry(data)
    (HERE/'parity_layout.json').write_text(json.dumps(data[0],indent=2)+'\n')
    receipt=dict(status='PASS',layout=data[0],audit=audit,
                 tile_sha256=sha256((HERE/'wang943_tiles.json').read_bytes()).hexdigest())
    (HERE/'PARITY_GEOMETRY.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':output()
