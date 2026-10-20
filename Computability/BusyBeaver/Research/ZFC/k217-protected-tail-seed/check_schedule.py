"""Independent bounded arithmetic check of the exact enumerator command schedule.
No supplied code, formula arithmetic, binary simulator, or compiler is invoked.
The all-natural claim is the separate ordinary induction in proof.md.
"""
from pathlib import Path
from math import isqrt
import hashlib,json,time
N=100000
out=Path(__file__).parent

def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    y=n-s*(s+1)//2
    return s-y,y

def second(n):return unpair(n)[1]
def pair(x,y):return (x+y)*(x+y+1)//2+y

def descriptor(n):
    tag,y=unpair(n)
    if tag<3:
        x,r=unpair(y)
        return ('MP','DROP','NIP')[tag], [x], r
    x,z=unpair(y); yy,z=unpair(z); u,r=unpair(z)
    return 'AX',[tag-3,x,yy,u],r

b=[];minimum=[];length=[];total=0;lowest=0;early=[];start=time.monotonic()
for n in range(N+1):
    name,args,r=descriptor(n)
    assert pair(*unpair(n))==n
    child=r-1
    assert r==0 or 0<=child<n
    effect={'MP':0,'DROP':1,'NIP':-1,'AX':10}[name]
    suffix_b=0 if r==0 else b[child]
    suffix_min=0 if r==0 else minimum[child]
    suffix_len=0 if r==0 else length[child]
    b.append(effect+suffix_b)
    minimum.append(min(0,effect+suffix_min))
    length.append(1+suffix_len)
    assert length[n]<=n+1
    assert total+minimum[n]>=0,(n,total,minimum[n])
    lowest=min(lowest,total+minimum[n]);total+=b[n]
    if n<20:early.append({'candidate':n,'first':[name,args], 'suffix':None if r==0 else child,'balance':b[n],'min_prefix':minimum[n],'commands':length[n],'cumulative':total})
assert b[0]==0 and minimum[0]==0
# Prefix-sum preservation under second-unpair, tested on the actual b sequence.
g=[0]+b
for iteration in range(3):
    g=[g[second(y)]for y in range(10001)]
    s=0
    for x in g:s+=x;assert s>=0
result={'status':'BOUNDED_SCHEDULE_CHECK_PASS','role':'Author independent finite arithmetic check; not binary/source interpreter or proof kernel.','highest_candidate_inclusive':N,'candidate_count':N+1,'primitive_commands':sum(length),'minimum_conservative_stack_balance':lowest,'final_conservative_stack_balance':total,'maximum_candidate_commands':max(length),'initial_candidate_zero_balance':b[0],'early_candidates':early,'pairing_checks':{'P_10_1':pair(10,1),'P_1_0':pair(1,0),'Q_0_F':4*pair(0,1)+2},'seconds':time.monotonic()-start,'reader_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'limits':['Bounded arithmetic check supports but does not prove the all-natural induction.','No formula values, theoremhood, binary startup, runtime, or actual complete AX continuation evaluated.']}
(out/'schedule-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('early_candidates','limits')}))
