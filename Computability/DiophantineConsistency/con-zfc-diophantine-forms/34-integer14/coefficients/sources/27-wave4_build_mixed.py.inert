"""Independently authored mixed-radix Wang943 coefficient construction.
All input files are inert JSON; no downloaded program is executed/imported.
"""
from pathlib import Path
import json, hashlib, gzip
P=Path(__file__).resolve().parent

def construct():
    rows=json.loads((P/'sources/k215_transitions.json').read_text())['transitions']
    sr=sorted({t for q,b,v,m,t in rows if m==1}); sl=sorted({t for q,b,v,m,t in rows if m==-1})
    rr={q:j+6 for j,q in enumerate(sr)}; ll={q:j+6+len(sr) for j,q in enumerate(sl)}
    hd=lambda q,b:2*(q+1)+b
    ts=set((0,hd(q,b),rr[t],v) if m==1 else (ll[t],hd(q,b),0,v) for q,b,v,m,t in rows)
    ts.update((0,hd(215,b),0,hd(215,b)) for b in (0,1))
    ts.update((0,b,0,b) for b in (0,1))
    ts.update((rr[q],b,0,hd(q,b)) for q in sr for b in (0,1))
    ts.update((0,b,ll[q],hd(q,b)) for q in sl for b in (0,1))
    ts.update((0,c,0,438) for c in (0,1,hd(215,0),hd(215,1)))
    ts.update([(2,434,2,0),(2,435,3,1),(3,436,4,hd(93,0)),(4,436,4,0)])
    ts.update((1,438,1,c) for c in (434,435,436))
    ts.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
    start=(2,435,3,1); forbidden=(5,0,0,0); ts.add(forbidden)
    tiles=[start,forbidden]+sorted(ts-{start,forbidden})
    assert len(tiles)==943 and len(sr)==199 and len(sl)==45
    old=json.loads((P/'upstream/compiler/wang943_tiles.json').read_text())
    assert [list(t) for t in tiles]==old
    copies={(j,t):offset+t for j,offset in enumerate([1023,1013,1003,983]) for t in range(10)}
    anchors=[1095,1096,2195,3296]
    support=set(range(943))|set(copies.values())|{1063,1064}|set(anchors)
    weights=[1<<(10+2*j) for j in range(44)]
    ce={i:1+sum(weights[10*j+t] for j,x in enumerate(tile) for t in range(10) if (x+512)>>t&1)+sum(weights[40:]) for i,tile in enumerate(tiles)}
    ce.update({e:weights[10*j+t] for (j,t),e in copies.items()})
    ce.update({e:weights[40+j] for j,e in enumerate(anchors)})
    ce.update({1063:0,1064:0})
    mu=1022+sum(weights)
    b,L,H,T1,T2=125,15625,42,7631,8733
    dc={t:1 for t in (30,H+20,1100,2200)}
    for e,c in ce.items():
        for T in (T1,T2):dc[T-e]=dc.get(T-e,0)+c
    dc={e:c for e,c in dc.items() if c}
    targets=[(1013+j,{983+j},set(),{1013+j}) for j in range(10)]
    targets += [(H+1023+j,{1003+j},{1023+j},set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    checks=0
    for t,d,r,y in targets:
        for e in support:
            assert dc.get(t-e,0)==int(e in d),(t,e,'dc')
            assert int(e+H==t)==int(e in r),(t,e,'dr')
            assert int(e==t)==int(e in y),(t,e,'temporal')
            checks+=3
    for T in (T1,T2):
        for e in support:
            assert dc.get(T-e,0)==ce[e]
            assert e+H!=T
            checks+=2
    assert {(T1-e)%L for e in support}.isdisjoint({(T2-e)%L for e in support})
    assert {(2195-e)%L for e in support}&{(3296-e)%L for e in support}=={0}
    mass=(len(support)+2)*(2*sum(ce.values())+6)
    assert 4*mass+8<1<<b and 2*mu+4<1<<b
    max_degree=max(max(dc)+max(support),H+max(support),max(support))
    padding_count=len(support)-(2*mu.bit_count()+len(targets)+1)
    padding=list(range(max_degree+1,max_degree+1+padding_count))
    assert padding_count==860 and max(padding)<L
    dc5=sum((c%5)*pow(2,e,5) for e,c in dc.items())%5
    dr5=pow(2,H,5)
    assert (2*dc5-dr5)%5==1
    scalar=dict(variant='wang943-mixed-radix4-zero-fields-5pow9',k=943,b=b,Lcell=L,d=b*L,H=H,T1=T1,T2=T2,copy_offsets=[1023,1013,1003,983],anchors=anchors,dummies=[1063,1064],bare_shifts=[30,H+20,1100,2200],mu=str(mu),mu_bit_length=mu.bit_length(),mu_population=mu.bit_count(),support_size=len(support),clause_coefficient_max_bit_length=max(ce.values()).bit_length(),mass_bit_length=mass.bit_length(),carry_threshold_bit_length=(4*mass+8).bit_length(),max_unshifted_degree=max_degree,padding_first=padding[0],padding_last=padding[-1],padding_count=padding_count,convolution_basis_checks=checks,DC_mod5=dc5,DR_mod5=dr5,rank_unit_mod5=(2*dc5-dr5)%5)
    return scalar,tiles,support,ce,mu,dc,targets,padding

def materialize(data):
    s,tiles,E,ce,mu,dc,targets,pad=data
    b=s['b'];d=s['d'];B=1<<d
    DC=sum(c<<(b*e) for e,c in dc.items()); DR=1<<(b*s['H'])
    MF=4+(mu<<(b*s['T1']))+(mu<<(b*s['T2']))+sum(1<<(b*t) for t,*_ in targets)+sum(1<<(b*t) for t in pad)
    MC=B-1-sum(1<<(b*e) for e in E if e!=1)-(2<<(b*1063))
    ports=dict(beta=B-1,K=DC+B*DR,MC=MC,MF_source=MF+B-1)
    assert MC%4==2 and MF%8==4 and 0<MF<B-1 and 0<MC<B-1
    assert MC.bit_count()+MF.bit_count()==d
    assert MF.bit_count()==len(E)==989
    assert DC<B and DC%5==s['DC_mod5'] and DR%5==s['DR_mod5']
    out=P/'expanded';out.mkdir(exist_ok=True)
    manifest={'encoding':'unsigned minimal-width little-endian','ports':{}}
    for name,n in ports.items():
        raw=n.to_bytes((n.bit_length()+7)//8,'little')
        (out/(name+'.bin')).write_bytes(raw)
        gz=gzip.compress(raw,mtime=0);(out/(name+'.bin.gz')).write_bytes(gz)
        assert int.from_bytes(raw,'little')==n and gzip.decompress(gz)==raw
        manifest['ports'][name]=dict(bit_length=n.bit_length(),bytes=len(raw),gzip_bytes=len(gz),sha256=hashlib.sha256(raw).hexdigest(),population=n.bit_count(),mod4=n%4,mod8=n%8,mod5=n%5)
    manifest.update(total_raw_bytes=sum(x['bytes'] for x in manifest['ports'].values()),total_gzip_bytes=sum(x['gzip_bytes'] for x in manifest['ports'].values()),MC_population=MC.bit_count(),MF_native_population=MF.bit_count(),population_sum=d,MF_native_mod8=MF%8,MC_mod4=MC%4)
    (out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest

if __name__=='__main__':
    data=construct();s,tiles,*_=data
    (P/'COEFFICIENTS.json').write_text(json.dumps(s,indent=2)+'\n')
    (P/'wang943_tiles.json').write_text(json.dumps(tiles,separators=(',',':'))+'\n')
    m=materialize(data)
    print(json.dumps({'scalars':s,'materialization':m},indent=2))
