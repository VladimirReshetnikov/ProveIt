"""New, standalone exact-integer checks; no inherited script or simulator imported."""
import json
from math import gcd, isqrt
from pathlib import Path

triples=[]
for c in range(2,201):
    for a in range(1,c):
        b=isqrt(c*c-a*a)
        if b and a*a+b*b==c*c and gcd(gcd(a,b),c)==1:
            triples.extend((sa*a,sb*b,c) for sa in (-1,1) for sb in (-1,1))
rows=0
composite=set()
for a,b,c in triples:
    if any(c%d==0 for d in range(2,isqrt(c)+1)):
        composite.add(c)
    C,S=1,0
    for n in range(21):
        P=c**n
        B=4*P+2*c+1
        H=a+abs(b)*B
        assert H >= 2
        assert C*C+S*S==P*P
        assert gcd(gcd(abs(C),abs(S)),P)==1
        assert abs(C)<=P and abs(S)<=P
        assert (pow(H,n,B*B+1)-C-B*S)%(B*B+1)==0
        assert 2*P*(B+1)<B*B+1
        assert 2*P<B
        # Recover q = c^n r canonically, including composite c.
        for r in (1,2,c-1,c+1,2*c+1):
            if r%c:
                q=P*r
                m=0
                rem=q
                while rem%c==0:
                    m+=1
                    rem//=c
                assert (m,rem)==(n,r)
                k,s=divmod(r,c)
                t=c-s
                assert k>=0 and s>0 and t>0 and r==c*k+s and s+t==c
        rows+=1
        C,S=a*C-abs(b)*S,abs(b)*C+a*S
result={'primitive_signed_ordered_triples_c_le_200':len(triples),
        'power_cases_n_0_through_20':rows,
        'composite_hypotenuses_tested':sorted(composite),
        'method':'fresh standard-library exact integer checks; no old code, symbolic engine, or simulator',
        'result':'all assertions passed'}
Path(__file__).with_name('arithmetic_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
