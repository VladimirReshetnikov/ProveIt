#!/usr/bin/env python3
"""Fresh finite checks of the Report 49 phase-derived frame obstruction.
Does not import or run the CA, any inherited checker, or any saved schedule.
"""
from pathlib import Path
import hashlib,json

def epoch(k): return k*k+3*k

def stationary(D,s):
    assert D>=13 and 0<=s<2*D-22
    if s<=D-11: return (0,5+s,6+s,D)
    return (0,2*D-18-s,2*D-14-s,D+1)

cases=slices=0
for k in range(1001):
    D=13+k
    assert epoch(k+1)-epoch(k)==2*D-22==2*k+4
    right=set();left=set()
    for s in range(2*D-22):
        z=stationary(D,s); t=epoch(k)+s; y=tuple(t+x for x in z)
        assert z[0]==0 and all(z[i]<z[i+1] for i in range(3))
        assert y[0]==t
        selected=(y[1]-y[0]==5 and y[2]-y[0]==6)
        assert selected==(s==0)
        if selected:
            assert y==(epoch(k),epoch(k)+5,epoch(k)+6,epoch(k)+13+k)
            slices+=1
        if z[2]-z[1]==1:
            assert z[3]==D and 5<=z[1]<=D-6
            right.add(z[1])
        else:
            assert z[2]-z[1]==4 and z[3]==D+1 and 5<=z[1]<=z[3]-9
            left.add(z[1])
        cases+=1
    assert right==set(range(5,D-5))
    assert left==set(range(5,D-7))

huge=0
for k in (10**10,10**30,10**60,10**100):
    D=13+k
    assert epoch(k+1)-epoch(k)==2*k+4
    for s in sorted({0,1,D-11,D-10,2*D-23}):
        z=stationary(D,s);t=epoch(k)+s;y=tuple(t+x for x in z)
        assert y[0]==t and all(y[i]<y[i+1] for i in range(3))
        assert ((y[1]-y[0],y[2]-y[0])==(5,6))==(s==0)
        huge+=1

out={'status':'PASS','scope':'Finite phase-formula fixtures, not proof by finite search and not CA execution',
'counts':{'complete_cycles':1001,'individual_times':cases,'selected_section_states':slices,'huge_integer_boundary_checks':huge},
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'upstream_code_executed':False,'saved_schedules_executed':False}
Path(__file__).with_name('CHECK-RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
