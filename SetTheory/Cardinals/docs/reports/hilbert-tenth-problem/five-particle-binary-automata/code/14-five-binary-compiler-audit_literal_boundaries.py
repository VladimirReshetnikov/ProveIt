"""All literal controls tested at geometric phase boundaries, not full traces."""
import hashlib,json
from pathlib import Path
from five_binary import BinaryCA,Machine

HERE=Path(__file__).parent
SOURCE=HERE/'source-replay'/'source'/'literal2.json'
raw=SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='85e16b44828f2f3d4ad6d0805dcc9e9922893a6d286874f2018d6a33af864b00'
data=json.loads(raw)
m=Machine(data['rows'],data['entry'],data['halt']);ca=BinaryCA(m)
counts={'controls':0,'minimum_counter_cases':0,'phase_boundary_steps':0}
for q,r in m.rows.items():
    assert r[0] in ('ADD','SUB')
    for c in (0,1):
        a,b=(c,0) if r[1]==0 else (0,c)
        x0=ca.encode(q,a,b);xf=ca.encode(*m.step(q,a,b))
        if r[0]=='SUB' and c==0:
            assert ca.step(x0)==xf and ca.duration(q,a,b)==1
            counts['phase_boundary_steps']+=1
        else:
            s=2*r[1]-1;delta=1 if r[0]=='ADD' else -1
            L=ca.Z+c;o=ca.codes['O',q];i=ca.codes['I',q]
            tout=L-ca.C-o-ca.K;tin=L+delta-ca.C-i-ca.K
            T=3+tout+tin
            assert ca.duration(q,a,b)==T
            oldmarks={-ca.Z-a,0,ca.Z+b}
            target=s*(L+delta);newmarks=oldmarks-{s*L}|{target}
            def state(t):
                if t==0:return x0
                if t==T:return xf
                if t<=1+tout:
                    k=t-1
                    return oldmarks|{s*(ca.C+k),s*(ca.C+o+k)}
                k=t-(2+tout)
                return newmarks|{target-s*(ca.C+k),target-s*(ca.C+i+k)}
            depart=ca.K-ca.C+2
            depart_return=2+tout+ca.K-ca.C+1
            times={0,1,depart-1,depart,depart+1,tout,1+tout,2+tout,
                   depart_return-1,depart_return,depart_return+1,T-3,T-2,T-1}
            for t in sorted(times):
                assert 0<=t<T
                old=state(t);expected=state(t+1)
                assert ca.step(old)==expected,(q,c,t)
                assert len(old)==len(expected)==5
                counts['phase_boundary_steps']+=1
        counts['minimum_counter_cases']+=1
    counts['controls']+=1
report={'status':'passed','source_sha256':hashlib.sha256(raw).hexdigest(),
        'compiler_sha256':hashlib.sha256((HERE/'five_binary.py').read_bytes()).hexdigest(),
        'counts':counts,'literal_ledger':ca.ledger(),
        'limitation':'Tests all actual literal controls at minimum-counter phase boundaries; does not certify the source machine universality or execute its entire long computations.'}
(HERE/'audit_literal_boundaries.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
