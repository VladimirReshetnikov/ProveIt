"""Independent audit of exact difference-set Wang943 compact geometry.
Uses inert, previously independently verified tile JSON; no builder imports.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'compiler'
raw=(BASE/'wang943_tiles.json').read_bytes()
assert sha256(raw).hexdigest()=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'
tiles=json.loads(raw)
k,A,b,L=943,1024,625,15625
rho=1<<b; d=b*L
copy=[[off+j for j in range(10)] for off in (1023,1013,1003,983)]
anchors=[1095,1096,2195,3296]
dummies=[1063,1064]
H,T1,T2=5497,7631,8733
bare=[30,5517,1100,2200]
E=set(range(k))|set(sum(copy,[]))|set(anchors)|set(dummies)
assert len(E)==989
c={}
for i,tile in enumerate(tiles):
    c[i]=1+sum((((label+512)>>bit)&1)*A**(1+10*slot+bit) for slot,label in enumerate(tile) for bit in range(10))+sum(A**j for j in range(41,45))
for slot in range(4):
    for bit in range(10): c[copy[slot][bit]]=A**(1+10*slot+bit)
for j,e in enumerate(anchors): c[e]=A**(41+j)
for e in dummies:c[e]=0
assert set(c)==E
mu=A-2+sum((A-3)*A**j for j in range(1,45))+(((1<<78)-1)<<450)
assert mu.bit_count()==483 and mu.bit_length()==528
raw_sum=sum(c.values())
assert raw_sum<A**45
assert max((raw_sum//A**j)%A for j in range(45))==944
mass=(len(E)+2)*(2*raw_sum+6)
threshold=max(4*mass+8,2*mu+4,16)
assert threshold<=rho and mass<=rho//4-2
DC=Counter({x:1 for x in bare})
for e,value in c.items():
    if value:
        DC[T1-e]+=value
        DC[T2-e]+=value
DR={H:1}
vertical=[(copy[1][j],copy[3][j],copy[1][j]) for j in range(10)]
horizontal=[(H+copy[0][j],copy[2][j],copy[0][j]) for j in range(10)]
anchor_tests=[(anchors[2],anchors[0],anchors[2]),(anchors[3],anchors[1],anchors[3])]
targets=vertical+horizontal+anchor_tests
horizontal_targets={r[0] for r in horizontal}
checks=0
for t,unshifted,neighbor in targets:
    for e in E:
        assert DC.get(t-e,0)==int(e==unshifted),(t,e,'DC',DC.get(t-e,0))
        assert DR.get(t-e,0)==int(t in horizontal_targets and e==neighbor)
        assert int(t==e)==int(t not in horizontal_targets and e==neighbor)
        checks+=3
for t in (T1,T2):
    for e in E:
        assert DC.get(t-e,0)==c[e],(t,e,'clause')
        assert DR.get(t-e,0)==0
        checks+=2
# Essential replacement for conservative interval separation:
# expanded support's translates cannot hit both clauses; no interval assumption.
Estar=E|{dummies[0]+1}
assert not ({(T1-e)%L for e in Estar}&{(T2-e)%L for e in Estar})
assert (T2-T1) not in {e-f for e in Estar for f in Estar}
anchor_rotations={(anchors[2]-e)%L for e in E}&{(anchors[3]-e)%L for e in E}
assert anchor_rotations=={0}
assert [(e,f) for e in E for f in E if f-e==anchors[3]-anchors[2]]==[(anchors[2],anchors[3])]
assert min(DC)>2
assert max(DC)+max(E)<L and H+max(E)<L
assert 3*rho//4+mass<=rho-2 and rho//2+1+mass<=rho-2
assert all(DC.get(t-e,0)==0 and DR.get(t-e,0)==0 and t!=e for e in dummies for t,_,_ in targets)
# Mask support is disjoint even though raw convolution bands overlap elsewhere.
field={2}
for t,_,_ in targets:
    assert b*t not in field
    field.add(b*t)
for t in (T1,T2):
    for bit in range(mu.bit_length()):
        if (mu>>bit)&1:
            assert b*t+bit not in field
            field.add(b*t+bit)
cleared={b*e for e in E if e!=1}|{b*dummies[0]+1}
assert len(field)==len(cleared)==989
assert max(field)<d-1 and max(cleared)<d-1
assert field&set(range(8))=={2} and cleared&set(range(4))=={0}
unit=(2*sum(value*pow(2,exponent,5) for exponent,value in DC.items())-pow(2,H,5))%5
assert unit==4
assert pow(2,dummies[0],5)*3*unit%5==1
assert b==5**4 and L==5**6 and d==5**10
receipt=dict(status='PASS',scope='Independent exact finite geometry and arithmetic-interface audit; universal difference-set argument is in companion note',
    b=b,L=L,d=d,native_support=len(E),anchors=anchors,bare_shifts=bare,Hc=H,T1=T1,T2=T2,
    gap=T2-T1,Emax=max(E),basis_convolution_checks=checks,
    all_rotation_clause_separation=True,anchor_rotations=sorted(anchor_rotations),
    unique_anchor_difference=1101,mod5_unit=unit,dummy_derivative_mod5=1,
    max_unshifted_degree=max(DC)+max(E),mass_bit_length=mass.bit_length(),threshold_bit_length=threshold.bit_length(),
    native_field_mask_population=len(field),data_mask_population=d-len(cleared),
    coefficient_bit_lengths={'beta':d,'K':b*(L+H)+1,'MC':d,'MF_source':d+1})
(ROOT/'audit/WANG943_COMPACT_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

# Independent byte construction; no imports of either materializer.
if (BASE/'coefficients_compact').is_dir():
    import gzip
    def set_bit(out,pos):out[pos//8]|=1<<(pos%8)
    def or_term(out,value,pos):
        byte,shift=divmod(pos,8); value<<=shift
        chunk=value.to_bytes((value.bit_length()+7)//8,'little')
        for j,v in enumerate(chunk):out[byte+j]|=v
    beta=bytearray([255])*((d+7)//8)
    beta[-1]&=(1<<(d%8 or 8))-1
    MC=bytearray(beta)
    for pos in cleared:MC[pos//8]&=255^(1<<(pos%8))
    K=bytearray((b*(L+H)+1+7)//8)
    for exp,value in DC.items():or_term(K,value,b*exp)
    set_bit(K,d+b*H)
    MF_source=bytearray((d+1+7)//8)
    for pos in (field-{2})|{0,1,d}:set_bit(MF_source,pos)
    results={}
    for name,wanted in [('beta',beta),('K',K),('MC',MC),('MF_source',MF_source)]:
        path=BASE/'coefficients_compact'/f'{name}.bin'
        actual=path.read_bytes(); assert actual==wanted,name
        gz=Path(str(path)+'.gz').read_bytes()
        assert gzip.decompress(gz)==actual
        results[name]=dict(bytes=len(actual),sha256=sha256(actual).hexdigest(),gzip_bytes=len(gz),gzip_sha256=sha256(gz).hexdigest())
    receipt['materialized_coefficients']=results
    receipt['materialized_total_bytes']=sum(row['bytes'] for row in results.values())
    receipt['compressed_total_bytes']=sum(row['gzip_bytes'] for row in results.values())
    (ROOT/'audit/WANG943_COMPACT_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'materialized_coefficients':results},indent=2))
