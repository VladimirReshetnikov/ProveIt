#!/usr/bin/env python3
"""Finite recurrence controls and a q-divisibility counterexample; no Lean."""
import gzip,hashlib,json,random
from math import comb
from pathlib import Path
D=Path(__file__).resolve().parents[2];H0=Path(__file__).resolve().parent
pins={
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'research/ordinary14-shifted-guard87-calibration/README.md':'005fd2c04cef4c997383bf373cc48acd326e829eb01ff4d30c218dadaf9f758a'}
for name,sha in pins.items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==sha
def load(path,sha):
    raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==sha
    return json.loads(raw)
cgraph=load(H0/'candidate.json','71073ea15ceeddac9d9bf9324238d03af346b5075eedb78351f29f19079d3862')
pgraph=load(D/'research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093')
assert cgraph['witnesses']==['X' if x=='w' else x for x in pgraph['witnesses']]
assert cgraph['fixed_numerals']==pgraph['fixed_numerals']
assert cgraph['source']==[row for row in pgraph['source'] if row[0]!='X'] and len(cgraph['source'])==73
known=set(cgraph['witnesses']+cgraph['fixed_numerals'])
for n,op,x,y in cgraph['source']:
    assert n not in known and op in ('+','-','*')
    assert all(isinstance(z,int) or z in known for z in (x,y));known.add(n)
needed={'out'}
for n,op,x,y in reversed(cgraph['source']):
    if n in needed:needed.update((x,y))
assert all(row[0] in needed for row in cgraph['source'])
assert all(x in needed for x in cgraph['witnesses']+cgraph['fixed_numerals'])
def calc(graph,env):
    d=env.copy()
    def val(x):return x if isinstance(x,int) else d[x]
    for n,op,x,y in graph['source']:
        u,v=val(x),val(y);d[n]=u*v if op=='*' else u+v if op=='+' else u-v
    return d
rng=random.Random(1473100)
for _ in range(100):
    oldenv={x:rng.randrange(-4,5) for x in pgraph['witnesses']+pgraph['fixed_numerals']}
    old=calc(pgraph,oldenv);newenv={x:oldenv[x] for x in cgraph['witnesses'] if x!='X'}
    newenv.update({x:oldenv[x] for x in cgraph['fixed_numerals']});newenv['X']=old['X']
    assert calc(cgraph,newenv)['out']==old['out']
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,meta in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw']==meta['sha256_raw'] and b115['ports'][n]['sha256_gzip']==meta['sha256_gzip']
    z=(p72/meta['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['sha256_gzip']
    raw=gzip.decompress(z);assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw']
    fixed[n]=int.from_bytes(raw,'little')
prime=1000000007;polys={x:[0,i+2] for i,x in enumerate(cgraph['witnesses'])}
polys.update({n:[x%prime] for n,x in fixed.items()})
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sign):return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
    return trim(z)
def val(x):return [x%prime] if isinstance(x,int) else polys[x]
for n,op,x,y in cgraph['source']:
    polys[n]=mul(val(x),val(y)) if op=='*' else add(val(x),val(y),1 if op=='+' else -1)
assert len(polys['out'])-1==100 and polys['out'][-1]!=0
def cp(p,n):
    x,y=1,0;delta=p*p-1
    for _ in range(n):x,y=p*x+delta*y,x+p*y
    return x,y
count=0;intervals=0;recovery_controls=0
for X in range(1,16):
    for Y in range(1,50):
        a=Y*(X+1);A=a+2;m=X*Y*Y;P=2*m+1;H=4*a+3
        difference=12*X*Y*(X+1)+9*X-2*(X+1)**2
        assert difference==X*(2*A-1)**2-(X+1)**2*(2*P) and difference>0
        assert (X+1)**2>=4*X
        for N in range(1,9):
            R=2*N+1;d,c=cp(A,R);tau,z=cp(P,N+1);k=2*z
            assert d*d-(A*A-1)*c*c==1 and tau*tau-m*(m+1)*k*k==1
            assert 2*c*X**N>k*(X+1)**(2*N)
            assert (d-2**R-a*c)%H==0 and d>=2**R+a*c
            if Y*k<c<(Y+1)*k:
                intervals+=1
                assert 2**R<=4*Y<H and 0<X<H
                if (d-X-a*c)%H==0:
                    recovery_controls+=1;assert X==2**R
            count+=1
assert intervals==24 and recovery_controls>0
# q=3 is intentionally a toy port; this is not a full graph zero or compact44.
N=17;R=2*N+1;X=2**R
Y=sum(comb(2*N,j)*X**(N-j) for j in range(N+1))//2
q=3; a=Y*(X+1);m=X*Y*Y;d,c=cp(a+2,R);tau,z=cp(2*m+1,N+1);k=2*z
assert R>=26 and R+1<q**4 and 2*(N+1)==R+1
assert Y%q**3==0 and X%q!=0 and Y*k<c<(Y+1)*k
assert k>=R+1 and (k-(R+1))%(4*m)==0 and (2*(N+1))%(q**4)==R+1
assert tau*tau-m*(m+1)*k*k==1 and d*d-((a+2)**2-1)*c*c==1
assert (d-X-a*c)%(4*a+3)==0
digest=hashlib.sha256(Y.to_bytes((Y.bit_length()+7)//8,'little')).hexdigest()
assert digest=='f4a97f4b243ae8b62c6c163f151e00aca018af63dd828955e94bae6cffc2751c'
print(json.dumps({'graph_operations':73,'graph_inputs':14,'graph_live':True,
    'signed_parent_substitutions':100,'degree_prime':prime,
    'weighted_ray_degree':len(polys['out'])-1,'weighted_ray_leader':polys['out'][-1],
    'finite_recurrence_controls':count,'interval_cases':intervals,
    'projection_recovery_controls':recovery_controls,'toy_q':q,'toy_R':R,
    'toy_Y_bits':Y.bit_length(),'toy_Y_sha256_little_endian':digest,
    'toy_q_cubed_divides_Y':True,'toy_q_does_not_divide_X':True,
    'scope':'external Pell estimates; toy control is not a full graph zero; no Lean'},sort_keys=True,indent=2))
