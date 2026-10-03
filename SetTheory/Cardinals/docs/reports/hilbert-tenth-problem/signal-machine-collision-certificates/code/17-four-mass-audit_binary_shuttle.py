#!/usr/bin/env python3
"""Independent local detector, de Bruijn certificate, and all-phase formula checks."""
import hashlib
import json
from math import isqrt
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]
certpath=BASE/'binary-radius6-conservation-certificate.json'
cert=json.loads(certpath.read_text())
table=[int(b) for b in cert['rule_bits_indexed_by_window']]
potential=cert['potential_by_vertex']
assert len(table)==8192 and len(potential)==4096

rules=[({0,1},{1,2}),({0,2},{-1,1}),({0,1,3},{-1,1,4}),({0,2,4},{0,3,4})]

def detector(c,y=0):
    # Independently determine just output y by exact guarded pattern detection.
    out=int(y in c)
    edits=[]
    for old,new in rules:
        span=max(old)
        for offset in old ^ new:
            a=y-offset
            needed=set(range(a-2,a+span+3))
            assert all(abs(z-y)<=6 for z in needed)
            actual=c & needed
            if actual=={a+z for z in old}:
                edits.append(int(offset in new)-int(offset in old))
    assert len(edits)<=1
    return out+sum(edits)

for w in range(8192):
    c={i-6 for i in range(13) if (w>>i)&1}
    assert table[w]==detector(c)
    assert table[w]-((w>>6)&1)==potential[w>>1]-potential[w&4095]

def independent_step(c):
    candidates={x+e for x in c for e in (-1,0,1)}
    return {y for y in candidates if detector(c,y)}

# Exact arbitrary-time state, derived without invoking the producer's orbit code.
def closed(d,t):
    b=2*d-11
    k=(isqrt(b*b+4*t)-b)//2
    T=k*k+b*k
    D=d+k
    s=t-T
    assert 0<=s<2*D-10
    if s<=D-6:
        return {0,3+s,4+s,D}
    return {0,2*D-9-s,2*D-7-s,D+1}

checks=0
pattern_checks=0
for d in (7,8,9,15,100,10**40+7):
    for k in (0,1,2,31,10**20,10**80):
        D=d+k
        T=k*k+(2*d-11)*k
        phases={0,1,D-7,D-6,D-5,D-4,2*D-13,2*D-12,2*D-11}
        if D<1000:
            phases.update(range(2*D-10))
        for s in sorted(phases):
            if not 0<=s<2*D-10:
                continue
            c=closed(d,T+s)
            assert independent_step(c)==closed(d,T+s+1)
            checks+=1
            hit=(c & set(range(5))=={0,3,4})
            assert hit==(s==0)
            pattern_checks+=1

# The rule is not reversible: two different configurations have the same image.
a={0,1,4,6}
b={1,2,3,5}
assert a!=b and independent_step(a)==b and independent_step(b)==b

# Check the unique natural root through exact discriminants, including enormous data.
quartic_checks=0
for x in (0,1,7,100,10**70):
    for k in (0,1,2,123,10**80):
        t=k*k+(2*x+3)*k
        discriminant=(2*x+3)**2+4*t
        assert isqrt(discriminant)==2*k+2*x+3
        assert isqrt(discriminant)**2==discriminant
        assert k*k+(2*x+3)*k-t==0
        # The next time cannot be a hit, because all consecutive hit gaps exceed one.
        assert isqrt(discriminant+4)**2!=discriminant+4
        quartic_checks+=1

result={'status':'PASS','independent_guarded_local_table_entries':8192,
        'independently_verified_potential_edges':8192,
        'all_phase_closed_form_transition_checks':checks,
        'anchored_pattern_exclusivity_checks':pattern_checks,
        'large_integer_quartic_discriminant_checks':quartic_checks,
        'largest_tested_section_index':str(10**80),
        'noninjective_pair':{'first_input':sorted(a),'second_input':sorted(b),'common_image':sorted(b)},
        'certificate_sha256':hashlib.sha256(certpath.read_bytes()).hexdigest(),
        'limits':'Exact finite certificate and local detector checks plus selected formula checks; mathematical orbit proof audited separately.'}
Path(__file__).with_name('binary-independent-audit-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
