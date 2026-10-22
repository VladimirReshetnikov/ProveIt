"""Independent T4 successor generation and exact finite coefficient bounds.

Reads literal transitions and the proposed tile list as data, never imports
the construction worker's code. Does not expand the four final coefficients.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import json, hashlib

ROOT=Path(__file__).resolve().parents[1]
rows=json.loads((ROOT/'bridge/sources/k215_transitions.json').read_text())['transitions']
delta={(q,b):(w,d,nq) for q,b,w,d,nq in rows}
delta.update({(215,b):(b,0,215) for b in (0,1)})
LEFT,START,RIGHT,VERT,HORIZ=434,435,436,437,438
phase={LEFT,START,RIGHT}
def payload(code):
    if code<434:
        z,b=divmod(code,2)
        return b,None if z==0 else z-1
    if code in phase:return 0,0 if code==START else None
    return 0,None
headless=[x for x in range(439) if payload(x)[1] is None]
headed=[x for x in range(439) if payload(x)[1] is not None]
assert len(headless)==6 and len(headed)==433
triples=list(product(headless,repeat=3))
for where in range(3):
    for head in headed:
        for pair in product(headless,repeat=2):
            row=list(pair);row.insert(where,head);triples.append(tuple(row))
assert len(triples)==len(set(triples))==46980

def successors(l,c,r):
    # Reject horizontal restrictions, then generate successors instead of
    # testing all 439 possibilities against the other worker's predicate.
    if c==VERT:
        return [] if r==VERT else [VERT]
    if r!=VERT and ((c==HORIZ)!=(r==HORIZ)):
        return []
    if c==HORIZ:return [LEFT,START,RIGHT]
    if c in phase:
        if l==VERT and c!=LEFT:return []
        if r==VERT and c!=RIGHT:return []
        if r!=VERT and (c,r) not in {(LEFT,LEFT),(LEFT,START),(START,RIGHT),(RIGHT,RIGHT)}:
            return []
    bit,state=payload(c)
    if state is not None:
        write,move,new=delta[state,bit]
        if move==-1 and l==VERT or move==1 and r==VERT:return []
    else:write=bit
    out=[HORIZ] if state in (None,215) else []
    if l==HORIZ or r==HORIZ:return out
    arrivals=[]
    for value,direction in ((l,1),(c,0),(r,-1)):
        b,q=payload(value)
        if q is not None and delta[q,b][1]==direction:arrivals.append(delta[q,b][2])
    assert len(arrivals)<=1
    code=write if not arrivals else 2*(arrivals[0]+1)+write
    return out+[code]

generated=[triple+(n,) for triple in triples for n in successors(*triple)]
assert len(generated)==len(set(generated))==37075
start=(LEFT,START,RIGHT,1); forbidden=(HORIZ,0,0,HORIZ)
ordered=[start,forbidden]+sorted(set(generated)-{start,forbidden})
literal=json.loads((ROOT/'bridge/t4_windows.json').read_text())
assert ordered==[tuple(row) for row in literal]
classes=Counter()
for l,c,r,n in generated:
    group=('headless0' if c==0 else 'headless1' if c==1 else
           'working_head' if 2<=c<432 else 'halt_head' if 432<=c<434 else str(c))
    classes[group]+=1
assert dict(classes)=={'headless0':9148,'headless1':9148,'working_head':8600,
                      'halt_head':110,'434':888,'435':4,'436':1750,'437':4793,'438':2634}

a,k,ell,p=439,37075,16,16983
M,Hc,T1,T2,L,b=43661,2228029,4586163,6943861,9765625,390625
emax=27*M; dummy=42343; d=b*L
copy_starts=[40587,40148,39709,38831]
copies={offset+u for offset in copy_starts for u in range(a)}
support=set(range(k))|copies|{dummy,M,3*M,9*M,27*M}
assert len(support)==38836
extended=support|{dummy+1}
assert { (T1-e)%L for e in extended }.isdisjoint({ (T2-e)%L for e in extended })
assert { (9*M-e)%L for e in support } & { (27*M-e)%L for e in support } == {0}
assert max(support)==emax and T2+2*emax+2<L
assert T2-T1==2*emax+4 and (T2-T1)%4==2
assert d==5**18 and b==5**8 and L==5**10
bare=(3*a,Hc+a,8*M,24*M)
targets=[]
for u in range(a):
    el,ec,er,en=[offset+u for offset in copy_starts]
    targets += [(ec,{en},set(),{ec}),
                (Hc+el,{ec},{el},set()),
                (Hc+ec,{er},{ec},set())]
targets += [(9*M,{M},set(),{9*M}),(27*M,{3*M},set(),{27*M})]
assert len({t for t,*rest in targets})==1319
for target,dc_expected,dr_expected,rotation_expected in targets:
    assert {target-offset for offset in bare if target-offset in support}==dc_expected
    assert ({target-Hc} if target-Hc in support else set())==dr_expected
    assert ({target} if target in support else set())==rotation_expected
    assert target<T1-emax
for band,other in ((T1,T2),(T2,T1)):
    assert {band-offset for offset in bare}.isdisjoint(support)
    assert all(other+source-band not in support for source in support)

# All finite scalar arithmetic is small enough to evaluate exactly. The
# enormous B and final coefficient numerals are deliberately not expanded.
A=2**ell; mu_top=4*a+4+p
mu=(A-2)+((1<<(ell*(mu_top+1)))-A)//(A-1)
assert mu_top==18743 and mu.bit_count()==18758
exponents=Counter()
for tile in ordered:
    for j,symbol in enumerate(tile):exponents[1+j*a+symbol]+=1
    for t in range(1,5):exponents[4*a+t]+=1
for j in range(4):
    for symbol in range(a):exponents[1+j*a+symbol]+=1
for t in range(1,5):exponents[4*a+t]+=1
coefficient_sum=k+sum(count*(1<<(ell*e)) for e,count in exponents.items())
npos=len(support)
mass_required=4*(npos+2)*(2*coefficient_sum+6)+8
assert max(mass_required,2*mu+4,16)<1<<b
field_population=2*mu.bit_count()+3*a+2+1
assert field_population==npos
assert 2*(ell-1+mu_top)+3*a+2==38835

# Modular computation without expanding rho powers or the final constants.
vmod={}
for j,tile in enumerate(ordered):
    vmod[j]=(1+sum(pow(2,ell*(1+i*a+symbol),5) for i,symbol in enumerate(tile))+
             sum(pow(2,ell*(4*a+t),5) for t in range(1,5)))%5
for j,offset in enumerate(copy_starts):
    for symbol in range(a):vmod[offset+symbol]=pow(2,ell*(1+j*a+symbol),5)
for t,anchor in enumerate((M,3*M,9*M,27*M),1):vmod[anchor]=pow(2,ell*(4*a+t),5)
vmod[dummy]=0
dc5=(sum(pow(2,b*e,5) for e in (3*a,Hc+a,8*M,24*M))+
     sum(value*(pow(2,b*(T1-e),5)+pow(2,b*(T2-e),5)) for e,value in vmod.items()))%5
unit=(2*dc5-pow(2,b*Hc,5))%5
assert unit==3

result={
 'independent_successor_generation':'exact ordered-list match',
 'triples':len(triples),'tiles':len(generated),'center_class_counts':dict(classes),
 'tile_file_sha256':hashlib.sha256((ROOT/'bridge/t4_windows.json').read_bytes()).hexdigest(),
 'native_support_size':npos,'mu_population':mu.bit_count(),
 'independent_field_targets_checked':len(targets),
 'native_field_population':field_population,'two_band_and_anchor_rotation_tests':True,
 'exact_mass_requirement_bits':mass_required.bit_length(),
 'exact_two_mu_plus_four_bits':(2*mu+4).bit_length(),
 'radix_bits':b,'cell_length':L,'B_exponent':d,
 'five_adic_unit':unit,
 'scope':'Independent exact finite alphabet, support, population, and carry-bound checks. Universal compiler/marked-plane/halting equivalences require the accompanying mathematical proof.'
}
(Path(__file__).parent/'INDEPENDENT_T4_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
