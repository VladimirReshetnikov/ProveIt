"""Independent reconstruction: no import or execution of any construction code.
Checks the new mixed-radix tuple and reproduces all four published package19
baseline coefficient hashes using the same inert ordered tile data.
"""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent
TILES=json.loads((P/'wang943_tiles.json').read_text())
E=list(range(943))+list(range(983,993))+list(range(1003,1033))+[1063,1064,1095,1096,2195,3296]
assert len(E)==len(set(E))==989
positions=[[1023+j for j in range(10)],[1013+j for j in range(10)],[1003+j for j in range(10)],[983+j for j in range(10)]]
assert hashlib.sha256((P/'wang943_tiles.json').read_bytes()).hexdigest()=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'

def coefficients(mixed):
    weight=lambda n:1024*4**n if mixed else 1024**(n+1)
    coeff={e:0 for e in E}
    for index,tile in enumerate(TILES):
        digits=[int(bit) for symbol in tile for bit in format(symbol+512,'010b')[::-1]]+[1]*4
        coeff[index]=1+sum(weight(n)*bit for n,bit in enumerate(digits))
    for slot,es in enumerate(positions):
        for n,e in enumerate(es):coeff[e]=weight(10*slot+n)
    for n,e in enumerate([1095,1096,2195,3296]):coeff[e]=weight(40+n)
    if mixed:mu=1022+sum(weight(n) for n in range(44))
    else:mu=1022+sum(1021*1024**n for n in range(1,45))+((1<<78)-1)*(1<<450)
    return coeff,mu

def calculate(mixed):
    c,mu=coefficients(mixed)
    b=125 if mixed else 625;H=42 if mixed else 5497;L=15625;d=b*L;B=1<<d
    sparse={}
    for e in E:
        for band in [7631,8733]:sparse[band-e]=sparse.get(band-e,0)+c[e]
    for e in [30,H+20,1100,2200]:sparse[e]=sparse.get(e,0)+1
    DC=sum(v*pow(2,b*e) for e,v in sparse.items())
    DR=pow(2,b*H)
    MF=4+mu*(pow(2,b*7631)+pow(2,b*8733))
    MF+=sum(pow(2,b*e) for e in list(range(1013,1023))+list(range(H+1023,H+1033))+[2195,3296])
    if mixed:MF+=sum(pow(2,b*e) for e in range(12030,12890))
    MC=B-1-sum(pow(2,b*e) for e in E if e!=1)-pow(2,b*1063+1)
    return dict(beta=B-1,K=DC+B*DR,MC=MC,MF_source=MF+B-1),sparse,c,mu,MF

ports,dc,c,mu,mf=calculate(True)
b=125;d=5**9;B=1<<d
manifest=json.loads((P/'expanded/MANIFEST.json').read_text())
for name,value in ports.items():
    raw=value.to_bytes((value.bit_length()+7)//8,'little')
    assert raw==(P/'expanded'/f'{name}.bin').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==manifest['ports'][name]['sha256']
assert ports['MC'].bit_count()+mf.bit_count()==d
assert ports['MC']%4==2 and mf%8==4 and mf.bit_count()==989
assert 0<mf<B-1 and 0<ports['MC']<B-1
# Coefficient-array checks independent of the construction program's target loop.
full=[0]*15625
for e,v in dc.items():full[e]=v
spec=[(1013+j,983+j,None,1013+j) for j in range(10)]
spec += [(1065+j,1003+j,1023+j,None) for j in range(10)]
spec += [(2195,1095,None,2195),(3296,1096,None,3296)]
checks=0
for target,center,right,time in spec:
    for e in E:
        actual=full[target-e] if 0<=target-e<len(full) else 0
        assert actual==int(e==center)
        assert int(e+42==target)==int(e==right)
        assert int(e==target)==int(e==time)
        checks+=3
for target in [7631,8733]:
    for e in E:
        assert full[target-e]==c[e] and e+42!=target
        checks+=2
assert {(7631-e)%15625 for e in E}&{(8733-e)%15625 for e in E}==set()
assert {(2195-e)%15625 for e in E}&{(3296-e)%15625 for e in E}=={0}
maxterm=max(e for e,v in dc.items() if v)+max(E)
assert maxterm==12029 and max(range(12030,12890))<15625
mass=(len(E)+2)*(2*sum(c.values())+6)
assert 4*mass+8<1<<125 and 2*mu+4<1<<125
# All selector counts, and then all possible local digit sums, exactly.
assert [n for n in range(944) if not n&1022]==[0,1]
assert [n for n in range(3) if not n&1]==[0,2]
# Exhaust every valid tile cell, including forbidden for decoder purposes,
# and check the complete arbitrary-precision clause bitmask, not only digits.
for i,tile in enumerate(TILES):
    cell=c[i]
    for slot,symbol in enumerate(tile):
        cell+=sum(c[positions[slot][j]] for j in range(10) if (symbol+512)>>j&1)
    cell+=sum(c[e] for e in [1095,1096,2195,3296])
    assert cell&mu==0
    # Flipping each one of44 copy/anchor bits must fail.
    p=list(sum(positions,[]))+[1095,1096,2195,3296]
    bits=[bool((symbol+512)>>j&1) for symbol in tile for j in range(10)]+[True]*4
    for e,on in zip(p,bits):assert (cell+(-c[e] if on else c[e]))&mu
# Random many-selector assignments exercise the low digit before high carries.
rng=random.Random(943125)
for _ in range(500):
    selected=rng.sample(range(943),rng.randrange(2,944))
    total=sum(c[e] for e in selected)
    total+=sum(c[e] for e in E if e>=943 and rng.randrange(2))
    assert total%1024==len(selected) and total&1022
# Baseline19 is independently reconstructed; this catches endian/binding errors.
old,_,_,_,_=calculate(False)
expected={
'beta':'40cc309fcb5dd2942c371d18be6d955d472e6b4c3604034b316194037ac16a5d',
'K':'e79f794af9565a7d824beb423bd03ee9ac117811b9b0e3a83ffe18f8a084de99',
'MC':'2e3107193f3b376fc3cfffdaa3ef547e6dd8dfdd4548519c0e33b5ffe2f2371d',
'MF_source':'8851b54fffd93780996de5f8c69315448e1369c3eea142428d2225a5149d1825'}
for name,n in old.items():
    assert hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'little')).hexdigest()==expected[name]
# Exact finite packing-population check with small repeated blocks satisfying
# the same residues, population balance, and data/mask disjointness.
packing_cases=0
for D in range(6,10):
    smallB=1<<D
    for mc in range(2,smallB,4):
        for native in range(4,smallB,8):
            if mc.bit_count()+native.bit_count()!=D:continue
            for N in [1,3]:
                q=smallB**N;J=(q-1)//(smallB-1);M=q*q
                tm=mc*J+1+q*(native*J-1)
                assert tm<M and tm.bit_count()==D*N+2
                allowed=(M-1)^tm
                for S in [0,allowed,allowed&0xaaaaaaaa,allowed&0x55555555]:
                    assert S&tm==0
                    R=(M-S)*(M-1)+tm
                    assert R==((M-1-S)*M+(S+tm))
                    assert R.bit_count()==3*D*N+2
                    packing_cases+=1
receipt=dict(status='PASS',independent_new_tuple_byte_match=True,published_package19_tuple_sha256_match=True,native_basis_checks=checks,all943_valid_cells_checked=True,copy_anchor_single_flip_rejections=943*44,selector_counts_exhausted=944,random_many_selector_cells=500,packing_population_cases=packing_cases,carry_threshold_bits=(4*mass+8).bit_length(),nativeMF_population=mf.bit_count(),mask_population_sum=d,unit_mod5=(2*(sum(v*pow(2,e,5) for e,v in dc.items())%5)-pow(2,42,5))%5)
(P/'INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
