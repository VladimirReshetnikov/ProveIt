"""Exact authored reduction checks. Saved circuits are inspected as data only."""
from pathlib import Path
from fractions import Fraction
from math import gcd
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parent
def require(test,label):
    if not test: raise RuntimeError(label)
def pell(A,n,mod=None):
    delta=A*A-1; x,y=1,0; b,c=A,1
    while n:
        if n&1:
            x,y=x*b+delta*y*c,x*c+y*b
            if mod: x%=mod; y%=mod
        b,c=b*b+delta*c*c,2*b*c
        if mod: b%=mod; c%=mod
        n//=2
    return x,y
def psi_recurrence(A,n):
    a,b=0,1
    for _ in range(n): a,b=b,2*A*b-a
    return a

def run():
    source=json.loads((ROOT/'scout.json').read_text()); static=[]
    pins={
        'complete85_auxiliary_bezout_projection.json':'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc',
        'complete86_ordinary_auxiliary_projection.json':'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6',
        'scout.json':'0004189e84fdc34e1ae7cbffa30a0e904ec6a0f15be18bcabebe242a303163f8'}
    for name,expected in pins.items():
        require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected,'source pin '+name)
    for form in source['forms']:
        parent=json.loads((ROOT/form['parent']).read_text())['packet']
        old={row[0]:row for row in parent['source']}; new={row[0]:row for row in form['source']}
        removed=set(old)-set(new); changed={v for v in new if old.get(v)!=new[v]}
        require(removed=={'hpm1','index_difference','norm_index','norm_product'},'literal deleted cone')
        require(changed=={'all_units'},'only retained product edge changes')
        require(new['all_units']==['all_units','*','norm_four','norm_transport'],'paid retained product')
        require(set(parent['witnesses'])-set(form['witnesses'])=={'h'},'witness removal')
        require(len(form['witnesses'])==17,'17 witnesses')
        require(sum(row[1]=='*' for row in form['source'])==form['ledger']['M'],'M count')
        require(len(form['source'])==form['ledger']['total'],'total count')
        static.append(dict(parent=form['parent'],rows=len(new),removed=sorted(removed),changed=sorted(changed)))

    # Independent binary powering versus a separately written recurrence.
    recurrence_cases=0
    for A in range(2,42):
        for n in range(80):
            x,y=pell(A,n)
            require(y==psi_recurrence(A,n),'binary vs recurrence')
            require(x*x-(A*A-1)*y*y==1,'Pell norm')
            recurrence_cases+=1

    # Exact modular projection, rank divisibility, and strong source identities.
    projection_cases=rank_cases=stepdown_cases=0
    for a in range(1,101):
        H=4*a+3; A=a+2
        for p in range(1,65):
            x,y=pell(A,p,H)
            require((x-a*y-pow(2,p,H))%H==0,'projection recurrence')
            projection_cases+=1
    for A in range(2,10):
        for p in range(2,9):
            c=pell(A,p)[1]; delta=A*A-1
            # Divisibility checked modulo c^2 without constructing enormous m-th units.
            for multiple in [1,2,3]:
                m=multiple*c*p; fmod,ymod=pell(A,m,c*c)
                require(ymod==0,'canonical normalized c^2 divisibility')
                require((fmod*fmod-1)%(c*c)==0,'ordinary f^2 divisibility')
                rank_cases+=1
    for A in range(2,8):
        for m in range(2,12):
            f=pell(A,m)[0]
            for k in range(1,m+1):
                target=pell(A,k,f)[0]
                for n in range(4*m):
                    congruent=pell(A,n,f)[0]==target
                    equivalent=(n-k)%(4*m)==0 or(n+k)%(4*m)==0
                    require(congruent==equivalent,'plus-sign stepdown')
                    stepdown_cases+=1

    # Small-index contradictions, exact rational constants and uniform c bound.
    require(Fraction(18**3,4*16**2*4096**2)<1,'p4 bound')
    require(Fraction(34**4,2*32**2*4096)<1,'p5 bound')
    for A in range(2,1002):
        require(psi_recurrence(A,6)>A*(A*A-1)**2,'p6 size premise')

    fixtures=[]
    for r in [5,9,13]:
        p=r*(2*r+1); d=r*r; n=(3*r*r+r)//2; v=(2*r+1)*(r+1)//2-1
        X=1<<p; Y=1<<v; a=Y*(X+1); A=a+2; delta=A*A-1; E=X*Y; H=4*a+3; P=2*X*Y*Y+1
        D,c=pell(A,p); tau,k0=pell(P,n); k=2*k0
        eta=c-k*Y; zeta=k-eta; numerator=D-a*c-X
        require(eta>0 and zeta>0,'strict ratio fixture')
        require(numerator%H==0 and numerator//H>1,'main gamma fixture')
        require(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'first norm fixture')
        require(D*D-delta*c*c==1,'main norm fixture')
        require(X%16==0 and Y%4096==0,'literal scaled fixture')
        require((k-p-1)%E==d-1>0,'nonintegral h defect fixture')
        fixtures.append(dict(r=r,p=p,n=n,defect=d,X_exponent=p,Y_exponent=v,
            q=16,X_scale_integer=True,Y_scale_integer=True,first_norm=1,main_norm=1,
            eta_positive=True,zeta_positive=True,gamma_positive=True,h_remainder=d-1,
            max_pell_coordinate_bits=max(D.bit_length(),tau.bit_length()),full_candidate=False,
            packing_input_transport_checked=False))

    bound_cases=[]
    for t in range(4,257):
        q=1<<t; r=q*q//2+1; p=r*(2*r+1); d=r*r; n=(p+d)//2; v=(2*r+1)*(r+1)//2-1
        require(r%4==1 and p%4==3,'family parity')
        require(p*(p-n)==d*(v+1),'exact dyadic ratio balance')
        require((2*q-1)*(q*q-1)<p<q**4-q**3,'exact pretyping bounds')
        require(p>=t and v>=3*t,'genuine scale exponents')
        # Compare bit lengths to avoid materializing 2^(p-v) when p is gigantic.
        require((4*p).bit_length()<=p-v,'uniform ratio error less than1')
        bound_cases.append(t)
    parity_cases=0
    for B in [16,32,64,256]:
        for J in range(2,102,2):
            q=(B-1)*J+1
            for F,Z,MC,MF in [(1,1,2,B+3),(7,2,6,B+11)]:
                R=(q*q-Z-q*F)*(q*q-1)+(MC+q*MF)*J
                require(q%2==1 and R%2==0,'odd q packing parity')
                parity_cases+=1
    return dict(status='PASS',scope='Proof reduction and scaled subsystem only; no full candidate or new bound',
        commit='3f4a974a5ddf12c46302fc5d2edafc3730277923',pins=pins,static_source=static,
        saved_schedule_executions=0,upstream_code_executions=0,
        recurrence_cases=recurrence_cases,projection_cases=projection_cases,canonical_rank_modular_cases=rank_cases,
        stepdown_cases=stepdown_cases,p6_bound_cases=1000,odd_q_packing_cases=parity_cases,
        materialized_scaled_subsystems=fixtures,parametric_scale_bound_cases=len(bound_cases),
        huge_family_pell_coordinates_materialized=False)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--expect',type=Path,help='Byte-compare canonical stdout with this saved receipt')
    ap.add_argument('--output',type=Path,help='Also create a new receipt outside this frozen packet')
    args=ap.parse_args()
    if args.output:
        target=args.output.resolve()
        require(not target.is_relative_to(ROOT),'Refusing output inside frozen packet')
        require(not target.exists(),'Output must be a fresh external path')
        if args.expect:require(target!=args.expect.resolve(),'Output cannot overwrite expected receipt')
    result=run(); output=(json.dumps(result,indent=2)+'\n').encode()
    if args.expect:require(args.expect.read_bytes()==output,'Saved receipt byte mismatch')
    if args.output:
        with args.output.open('xb') as f:f.write(output)
    print(output.decode(),end='')
