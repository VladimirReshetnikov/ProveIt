#!/usr/bin/env python3
"""Independent full-matrix replay of directed pressure traces.
Uses only Python integers/Fraction; does not import the producer.
"""
import gzip,json,math,sys,time,hashlib
from fractions import Fraction as F
from pathlib import Path
sys.set_int_max_str_digits(0)
def need(ok,msg):
    if not ok:raise ArithmeticError(msg)
def mv(A,x):return [sum(a*b for a,b in zip(row,x)) for row in A]
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def ceilrat(a,b):return -((-a)//b)
def binom(n,k):return math.comb(n,k) if 0<=k<=n else 0
def weighted(x):return x[0]+2*sum(x[1:])
def norm(x):return abs(x[0])+2*sum(map(abs,x[1:]))
def interval_product(x,y):
    z=[x[i]*y[j] for i in range(2) for j in range(2)]
    return min(z),max(z)
def audit(path, out):
    start=time.time();path=Path(path);cert=json.loads(path.read_text())
    m=cert["m"];need(m>=2,"m scope");d=2*m;N=d-1;D=1<<(d-1);c=m-1
    with gzip.open(str(path)+".trace.gz","rt") as f:
        header=f.readline().split();need(header[:3]==["TMPRES1",str(m),str(d)],"header")
        precision=int(header[3]);scale=int(f.readline())
        norms=list(map(int,f.readline().split()));need(len(norms)==4,"norm metadata")
        trace=[list(map(int,line.split())) for line in f if line.strip()]
    fact=math.factorial(N);need(scale==(1<<precision)*fact**5,"grid")
    top=3*d-2;need(len(trace)==top+1,"trace coverage")
    need(cert["checked_response_orders"]==top,"certificate order coverage")
    fullB=[[binom(d,m+2*k-r) for r in range(-c,c+1)] for k in range(-c,c+1)]
    for r in range(N):need(sum(fullB[k][r] for k in range(N))==D,"column stochasticity")
    # Eulerian polynomials from the insertion recurrence.
    euler={1:[1]}
    for p in range(2,N+1):
        prev=euler[p-1]
        euler[p]=[(k+1)*(prev[k] if k<len(prev) else 0)+(p-k)*(prev[k-1] if k else 0) for k in range(p)]
    E=[[0]*N for _ in range(N)]
    for r in range(N):
        column=mul([(-1)**k*math.comb(r,k) for k in range(r+1)],euler[N-r])
        for i,value in enumerate(column):E[i][r]=value
    S=[[0]*N for _ in range(N)]
    for i in range(N):
        poly=[1]
        for h in range(-i,N-i):poly=mul(poly,[h,1])
        for r in range(N):S[r][i]=poly[N-r]
    for r in range(N):
        col=[E[i][r] for i in range(N)]
        need(mv(S,col)==[fact if i==r else 0 for i in range(N)],"full inverse")
        need(mv(fullB,col)==[(D>>r)*x for x in col],"full eigensystem")
    L=1
    for r in range(1,N):L=math.lcm(L,(1<<r)-1)
    weights=[0]+[(1<<r)*(L//((1<<r)-1)) for r in range(1,N)]
    Be=[[fullB[c+k][c+r]+(fullB[c+k][c-r] if r else 0) for r in range(m)] for k in range(m)]
    Bo=[[fullB[c+k][c+r]-(fullB[c+k][c-r] if r else fullB[c+k][c+r]) for r in range(m)] for k in range(m)]
    Tden=fact*L
    Te=[[sum(E[c+k][r]*weights[r]*(S[r][c+j]+(S[r][c-j] if j else 0)) for r in range(2,N,2)) for j in range(m)] for k in range(m)]
    To=[[sum(E[c+k][r]*weights[r]*(S[r][c+j]-S[r][c-j]) for r in range(1,N,2)) for j in range(1,m)] for k in range(1,m)]
    ae=max(F(sum((1 if i==0 else 2)*abs(Te[i][j]) for i in range(m)),(1 if j==0 else 2)*Tden) for j in range(m))
    ao=max(F(sum(abs(To[i][j]) for i in range(m-1)),Tden) for j in range(m-1))
    need(ae==F(norms[0],norms[1]) and ao==F(norms[2],norms[3]),"full-matrix parity norms")
    K=[[sum((-1)**u*binom(m+k,u)*binom(m-k,j-u) for u in range(j+1)) for k in range(m)] for j in range(d+1)]
    print(f"m {m}: full spectral norms checked",flush=True)
    del E,S,Te,To,fullB
    vectors=[];errors=[];ells=[];radii=[];ys=[];unorm=[]
    initial=euler[N][c:]
    new_trace=[]
    for order,row in enumerate(trace):
        need(len(row)==m+4 and row[0]==order,"trace row")
        _,old_error,lam,old_radius,*vec=row
        need(old_error>=0 and old_radius>=0,"stored nonnegative radii")
        bu=mv(Bo if order%2 else Be,vec)
        if order==0:
            need(old_error==old_radius==0 and lam==scale,"initial scalar")
            need(vec==[x*scale//fact for x in initial],"initial Eulerian vector")
            need(weighted(vec)==scale,"initial normalization")
            err=rad=0
        else:
            need((vec[0]==0) if order%2 else (weighted(vec)==0),"exact parity normalization")
            rn=[sum(K[j][k]*ys[order-j][k] for j in range(1,min(order,d)+1)) for k in range(m)]
            eb=sum(binom(d,j)*errors[order-j] for j in range(1,min(order,d)+1))
            if order%2 or order<d:
                need(lam==0,"structural scalar zero");rad=0
            else:
                need(lam==weighted(rn)//D,"scalar center");rad=eb+1
            rhs=[scale*x for x in rn];prod_error=0
            for j in range(d,order,2):
                h=order-j
                rhs=[x-D*ells[j]*y for x,y in zip(rhs,vectors[h])]
                prod_error+=abs(ells[j])*errors[h]+radii[j]*unorm[h]+radii[j]*errors[h]
            erhs=eb+ceilrat(prod_error,scale)
            projected_sum=weighted(rhs) if not order%2 else 0
            defect=[fact*(scale*(D*x-y)-z)+projected_sum*e
                    for x,y,z,e in zip(vec,bu,rhs,initial)]
            if order%2:need(defect[0]==0,"odd residual parity")
            else:need(weighted(defect)==0,"projected residual sum")
            defect_norm=norm(defect);defect_den=fact*D*scale
            alpha=ao if order%2 else ae
            err=ceilrat(alpha.numerator*(erhs*defect_den+defect_norm),
                        alpha.denominator*defect_den)
        vectors.append(vec);errors.append(err);ells.append(lam);radii.append(rad)
        ys.append(bu);unorm.append(norm(vec))
        new_trace.append([order,str(err),str(rad)])
    print(f"m {m}: all {top+1} projected residual enclosures propagated",flush=True)
    # Scalar pressure conversion independently generated from the tangent ODE.
    degree=3*d-2;limit=3*m-1
    choose=[[math.comb(n,j) for j in range(n+1)] for n in range(degree+1)]
    tanjet=[0]*(degree+2);tanjet[1]=1
    for n in range(2,degree+1,2):
        tanjet[n+1]=sum(choose[n][j]*tanjet[j]*tanjet[n-j] for j in range(1,n,2))
    powers=[[0]*(limit+1) for _ in range(limit+1)];powers[0][0]=1
    for j in range(1,limit+1):
        for k in range(j,limit+1):
            powers[j][k]=sum(choose[2*k][2*s]*tanjet[2*s+1]*powers[j-1][k-s] for s in range(1,k-j+2))
    lam_intervals=[]
    for j in range(limit+1):
        center=(-1)**j*ells[2*j];radius=radii[2*j]
        lam_intervals.append((center-radius,center+radius))
    logs=[(0,0)]*(limit+1)
    for j in range(m,limit+1):
        lo=2*scale*lam_intervals[j][0];hi=2*scale*lam_intervals[j][1]
        for k in range(m,j-m+1):
            plo,phi=interval_product(lam_intervals[k],lam_intervals[j-k])
            lo-=phi;hi-=plo
        logs[j]=(lo,hi)
    bounds=[];strict=0
    for k in range(m,limit+1):
        lo=hi=-4*m*scale*scale*tanjet[2*k-1]
        for j in range(m,k+1):
            lo+=logs[j][0]*powers[j][k];hi+=logs[j][1]*powers[j][k]
        den=2*scale*scale*math.factorial(2*k)
        need(lo<=hi,"interval order")
        if k==m:need(lo<=0<=hi,"missing coefficient")
        else:need(lo>0,"fresh residual lower endpoint");strict+=1
        divisor=math.gcd(math.gcd(lo,hi),den)
        bounds.append({"degree":2*k,"lower_numerator":str(lo//divisor),
                       "upper_numerator":str(hi//divisor),"denominator":str(den//divisor)})
    new_trace_path=Path(str(out)+".radii.gz")
    with gzip.open(new_trace_path,"wt") as f:
        json.dump({"m":m,"scale":str(scale),"fresh_error_radii":new_trace},f,separators=(",",":"))
    result={"m":m,"method":"independent exact projected residual enclosures",
        "trace_orders":top+1,"strict_pressure_degrees":strict,
        "full_spectral_norms_verified":True,"pressure_conversion":"independent tangent ODE derivative jets",
        "pressure_bounds":bounds,"all_strict_lower_endpoints_positive":True,
        "seconds":time.time()-start,"source_certificate_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
        "source_trace_sha256":hashlib.sha256(Path(str(path)+".trace.gz").read_bytes()).hexdigest(),
        "new_radii_sha256":hashlib.sha256(new_trace_path.read_bytes()).hexdigest()}
    Path(out).write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"m":m,"fresh_positive_degrees":strict,"seconds":result["seconds"]}),flush=True)
    return result
if __name__=="__main__":
    need(len(sys.argv)==3,"usage certificate.json audit.json")
    audit(sys.argv[1],sys.argv[2])

