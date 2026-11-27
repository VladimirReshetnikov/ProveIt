"""Independent exhaustive checks for hidden alternating forms in dimension four.

Only Python's standard library is used. Planes are constructed as actual row
spaces, and nonsingularity is checked by Gaussian elimination of 4x4 matrices.
The q=2 span process is enumerated exactly with integer counts.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import product, combinations
import json
from pathlib import Path

PAIRS=list(combinations(range(4),2))

def rank_rref(rows,q):
    a=[list(x) for x in rows]
    if not a:return ()
    m,n=len(a),len(a[0]);r=0
    for j in range(n):
        p=next((i for i in range(r,m) if a[i][j]%q),None)
        if p is None:continue
        a[r],a[p]=a[p],a[r]
        c=pow(a[r][j],-1,q);a[r]=[(x*c)%q for x in a[r]]
        for i in range(m):
            if i!=r and a[i][j]%q:
                c=a[i][j];a[i]=[(x-c*y)%q for x,y in zip(a[i],a[r])]
        r+=1
        if r==m:break
    return tuple(tuple(row) for row in a[:r])

def canonical(v,q):
    c=next((x for x in v if x),None)
    if c is None:return None
    c=pow(c,-1,q)
    return tuple(x*c%q for x in v)

def matrix(h,q):
    a=[[0]*4 for _ in range(4)]
    for v,(i,j) in zip(h,PAIRS):a[i][j]=v;a[j][i]=-v%q
    return a

def get_data(q):
    vectors=list(product(range(q),repeat=4))
    planes=set()
    for i,x in enumerate(vectors[1:]):
        for y in vectors[1:]:
            rr=rank_rref([x,y],q)
            if len(rr)==2:planes.add(rr)
    wedges={canonical(tuple((x[i]*y[j]-x[j]*y[i])%q for i,j in PAIRS),q)
            for x,y in planes}
    assert len(wedges)==len(planes)
    forms={canonical(h,q) for h in product(range(q),repeat=6) if any(h)}
    nonsing=sorted(h for h in forms if len(rank_rref(matrix(h,q),q))==4)
    wedges=sorted(wedges)
    masks=[sum((1<<j) for j,z in enumerate(wedges)
               if sum(x*y for x,y in zip(h,z))%q==0) for h in nonsing]
    counts=Counter(m.bit_count() for m in masks)
    p=Fraction(q**2-1,q**3-1)
    assert counts=={int(p*len(planes)):len(nonsing)}
    pair_hist=Counter((m&v).bit_count() for m in masks for v in masks)
    first_hist=Counter((masks[0]&v).bit_count() for v in masks)
    assert pair_hist=={k:v*len(nonsing) for k,v in first_hist.items()}
    # Test the proposed eigenvector formula independently on every partner
    # of the first nonsingular form, including the proportional pair.
    hm=matrix(nonsing[0],q);den=(q**4-1)*(q**4-q)
    eigen_hist=Counter()
    for g,gm in zip(nonsing,masks):
        gmat=matrix(g,q)
        dims=[]
        for a in range(q):
            diff=[[(gmat[i][j]-a*hm[i][j])%q for j in range(4)] for i in range(4)]
            dims.append(4-len(rank_rref(diff,q)))
        e=sum(q**k-1 for k in dims)
        pred=Fraction(e*(q**3-q)+(q**4-1-e)*(q**2-q),den)
        actual=Fraction((masks[0]&gm).bit_count(),len(planes))
        assert pred==actual,(q,g,dims,pred,actual)
        eigen_hist[tuple(dims)]+=1
    # Recovery must exclude *all* alternating competitors, not only
    # nonsingular ones. Check all projective forms and the zero form.
    rho=Fraction(2*q-1,q*q);K=4*q*(q-1)
    all_hist=Counter();conditional_max=Fraction(0)
    for g in [tuple([0]*6)]+sorted(forms):
        gmat=matrix(g,q);dims=[]
        for a in range(q):
            diff=[[(gmat[i][j]-a*hm[i][j])%q for j in range(4)] for i in range(4)]
            dims.append(4-len(rank_rref(diff,q)))
        e=sum(q**k-1 for k in dims)
        pred=Fraction(e*(q**3-q)+(q**4-1-e)*(q**2-q),den)
        gmask=sum(1<<j for j,z in enumerate(wedges) if sum(x*y for x,y in zip(g,z))%q==0)
        common=(masks[0]&gmask).bit_count()
        actual=Fraction(common,len(planes))
        assert pred==actual
        s=4-max(dims)
        assert actual/(p*p)<=1+Fraction(K,q**s)
        if any(g) and g!=nonsing[0]:
            cond=actual/p
            assert cond<=rho
            conditional_max=max(conditional_max,cond)
        all_hist[common]+=1
    result={"q":q,"dimension":4,"alternating_dimension":6,
       "planes":len(planes),"projective_nondegenerate_forms":len(nonsing),
       "isotropic_planes_per_form":int(p*len(planes)),"p":str(p),
       "ordered_pair_common_plane_histogram":dict(sorted(pair_hist.items())),
       "fixed_H_partner_common_plane_histogram":dict(sorted(first_hist.items())),
       "fixed_H_kernel_dimension_histogram":{";".join(map(str,k)):v for k,v in sorted(eigen_hist.items())},
       "all_partner_overlap_formulas_verified":len(nonsing),
       "all_alternating_competitors_including_zero_verified":len(forms)+1,
       "all_competitor_common_plane_histogram":dict(sorted(all_hist.items())),
       "maximum_nonproportional_conditional_overlap":str(conditional_max),
       "rho_bound":str(rho),"far_rank_bound_constant":K}
    return result,wedges,nonsing

def insert_binary(basis,x):
    # Unique reduced basis, highest pivot first.
    for b in basis:
        p=b.bit_length()-1
        if (x>>p)&1:x^=b
    if not x:return basis
    p=x.bit_length()-1
    a=[(b^x if (b>>p)&1 else b) for b in basis]+[x]
    return tuple(sorted(a,reverse=True))

def binary_span_law(wedges,forms,tmax=24):
    zs=[sum(v<<i for i,v in enumerate(z)) for z in wedges]
    hs=[sum(v<<i for i,v in enumerate(h)) for h in forms]
    states=[()];idx={():0};trans=[];zcounts=[]
    for basis in states:
        zcounts.append(sum(all((h&b).bit_count()%2==0 for b in basis) for h in hs))
        cs=Counter()
        for z in zs:
            bb=insert_binary(basis,z)
            if bb not in idx:idx[bb]=len(states);states.append(bb)
            cs[idx[bb]]+=1
        trans.append(list(cs.items()))
    cur=[0]*len(states);cur[0]=1;records=[]
    N=len(zs);M=len(hs);I=15
    for t in range(tmax+1):
        qt=N**t;pt=M*I**t
        assert sum(cur)==qt
        assert sum(c*z for c,z in zip(cur,zcounts))==pt
        tv=Fraction(sum(c*abs(z*qt-pt) for c,z in zip(cur,zcounts)),2*qt*pt)
        chi2=Fraction(sum(c*z*z for c,z in zip(cur,zcounts))*qt,pt*pt)-1
        # Independent all-pairs second-moment formula, using the observed
        # incidence histogram rather than the span-chain calculation.
        pair_chi2=(Fraction(7,3)**t+15*Fraction(49,45)**t+12*Fraction(7,9)**t)/28-1
        assert chi2==pair_chi2
        recovery=Fraction(sum(c*z for c,z,b in zip(cur,zcounts,states) if len(b)==5),pt)
        unique_nondeg=Fraction(sum(c for c,z in zip(cur,zcounts) if z==1),pt)
        q_impossible=Fraction(sum(c for c,z in zip(cur,zcounts) if z==0),qt)
        ranks=Counter()
        for c,b in zip(cur,states):ranks[len(b)]+=c
        records.append({"t":t,"tv":str(tv),"tv_decimal":float(tv),
            "chi_square":str(chi2),"gaussian_recovery_probability":str(recovery),
            "gaussian_recovery_decimal":float(recovery),
            "unique_nondegenerate_probability":str(unique_nondeg),
            "Q_no_compatible_nondegenerate":str(q_impossible),
            "Q_rank_counts":dict(sorted(ranks.items()))})
        if t<tmax:
            nxt=[0]*len(states)
            for i,c in enumerate(cur):
                if c:
                    for j,mult in trans[i]:nxt[j]+=c*mult
            cur=nxt
    return {"reachable_spans":len(states),"span_rank_histogram":dict(sorted(Counter(map(len,states)).items())),
            "exact_sequence_counts_and_likelihoods_verified":True,"records":records}

def main():
    all_data=[]
    for q in [2,3]:
        row,zs,hs=get_data(q)
        if q==2:row["exact_span_process"]=binary_span_law(zs,hs)
        all_data.append(row)
    out=Path(__file__).resolve().parents[1]/'data/independent_hidden_forms.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(all_data,indent=2)+'\n')
    print(json.dumps({"passed":True,"output":str(out),"summary":[{k:v for k,v in row.items() if k!='exact_span_process'} for row in all_data]},indent=2))
    print('t, TV, Gaussian recovery')
    for x in all_data[0]['exact_span_process']['records']:
        print(x['t'],x['tv_decimal'],x['gaussian_recovery_decimal'])

if __name__=='__main__':main()
