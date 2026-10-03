#!/usr/bin/env python3
"""Finite independent checks for the general-cap analytic barrier.
Not a proof: exercises the exact rank identities and the uniform bounds.
"""
import json, math, random
rng=random.Random(271828)
results={}
for b in range(3,9):
    a=(b-1)/b
    worst_rank=0.0
    worst_shift=0.0
    worst_scaled_residual=0.0
    total=0
    for v in (0.01,0.1,1.0,3.0,10.0,100.0,10000.0):
        E=[1.0]
        term=1.0
        for j in range(1,b+1):
            term*=v/j
            E.append(E[-1]+term)
        X=E[b]; q=math.log(X)
        p=[q]+[math.log(E[b-j]) for j in range(1,b)]+[0.0]
        Y=[E[b-j] for j in range(b+1)]+[0.0]
        rho=[1.0]+[X*Y[j+1]/(Y[1]*Y[j]) for j in range(1,b)]+[0.0]
        qv=Y[1]/X
        rhoq=[0.0]+[rho[j]*(qv+Y[j+2]/Y[j+1]-Y[2]/Y[1]-Y[j+1]/Y[j])/qv for j in range(1,b)]+[0.0]
        qp=Y[1]*(-math.expm1(-q))/q
        for trial in range(120):
            N=[rng.randrange(1,6)]+[rng.randrange(0,7) for _ in range(1,b)]
            groups=[j for j in range(b-1,-1,-1) for _ in range(N[j])]
            m=len(groups); k=rng.randrange(m)
            D=sum(rho[j]*N[j] for j in range(b))
            Dq=sum(rhoq[j]*N[j] for j in range(b))
            h=[0.0]; hq=[0.0]
            for j in groups:
                h.append(h[-1]+rho[j]); hq.append(hq[-1]+rhoq[j])
            r=h[k]/D
            rq=(hq[k]-r*Dq)/D
            lam=qp*D
            exact=0.0
            for i,j in enumerate(groups):
                asc=int(i>=k)
                childN=N.copy(); childN[j]-=1
                if j+1<b: childN[j+1]+=1
                childN[0]+=asc
                childgroups=[l for l in range(b-1,-1,-1) for _ in range(childN[l])]
                childk=i+int(j<b-1)
                Dc=sum(rho[l] for l in childgroups)
                Hc=sum(rho[l] for l in childgroups[:childk])
                assert math.isclose(Dc,D-rho[j]+rho[j+1]+asc,rel_tol=3e-14)
                assert math.isclose(Hc,h[i]+rho[j+1],rel_tol=3e-14,abs_tol=3e-14)
                rc=Hc/Dc
                shift=abs(rc-h[i]/D)*D
                worst_shift=max(worst_shift,shift)
                assert shift<=4+1e-10
                if asc:
                    loss=r-rc
                    worst_rank=max(worst_rank,loss)
                    assert loss<=1/(D+1)+1e-12
                exact+=math.exp(p[j+1]-p[j]+q*asc+q*(r-rc))
                total+=1
            residual=lam-qp*(r+q*rq)-exact
            scaled=abs(residual)/((1+q)*math.exp((a+0.5)*q))
            worst_scaled_residual=max(worst_scaled_residual,scaled)
    results[b]={"transitions_checked":total,"max_ascent_rank_loss":worst_rank,"max_D_times_rank_shift":worst_shift,"max_scaled_residual":worst_scaled_residual}
print(json.dumps(results,indent=2))
