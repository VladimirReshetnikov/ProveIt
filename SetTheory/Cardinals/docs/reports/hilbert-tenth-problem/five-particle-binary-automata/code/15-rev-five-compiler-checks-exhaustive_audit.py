"""Exhaustive periodic check of the isolation lemma, B=1, two nontranslate codes."""
N=17
FULL=(1<<N)-1
B=1
L=4
M=6

def shift(x,d):
    d%=N
    return ((x<<d)|(x>>(N-d)))&FULL

def mask(a, offsets):
    return sum(1<<((a+d)%N) for d in offsets)

cores=[mask(a,range(-B,B+1)) for a in range(N)]
halos=[mask(a,range(-L,L+1)) for a in range(N)]
neighbors=[mask(a,[d for d in range(-M,M+1) if d]) for a in range(N)]
codes=[[mask(a,offs) for a in range(N)] for offs in [(-1,0),(-1,1)]]

def apply(x):
    r0=shift(x,1)&x&~shift(x,-1)&FULL
    r1=shift(x,1)&~x&shift(x,-1)&FULL
    raw=r0|r1
    elig=0
    y=x
    todo=raw
    while todo:
        bit=todo&-todo
        todo^=bit
        a=bit.bit_length()-1
        label=0 if bit&r0 else 1
        if not raw&neighbors[a] and x&halos[a]==codes[label][a]:
            elig|=bit
            y=(y&~cores[a])|codes[1-label][a]
    return raw,elig,y

changed=eligible_configurations=0
for x in range(1<<N):
    raw,elig,y=apply(x)
    raw2,elig2,z=apply(y)
    assert raw2==raw,("raw",x,y,raw,raw2)
    assert elig2==elig,("eligible",x,y,elig,elig2)
    assert z==x,("involution",x,y,z)
    assert y.bit_count()==x.bit_count(),("mass",x,y)
    changed+=x!=y
    eligible_configurations+=bool(elig)
print(f"PASS: all {1<<N:,} periodic configurations of length {N}; {changed:,} changed configurations; raw keys, eligibility, involution and mass all preserved.")
