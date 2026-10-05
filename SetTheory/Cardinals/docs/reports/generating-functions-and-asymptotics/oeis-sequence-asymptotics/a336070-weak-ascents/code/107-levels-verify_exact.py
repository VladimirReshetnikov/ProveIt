#!/usr/bin/env python3
"""Fail-closed, standalone report107 finite exact verifier (Python stdlib only).

    python3 verify_exact.py
    python3 -O verify_exact.py
    python3 verify_exact.py --fixtures OTHER.json

Mathematical checks use int and fractions.Fraction, never float, log, or a
numerical tolerance. q=-M log(r) is symbolic and cancels after division by q;
at q=0 normalized limits and the actual zero corrector are distinguished.
No assertion is a correctness gate. Finite checks are not analytic proofs.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json
import re
import sys

HERE = Path(__file__).resolve().parent
MS = (1,2,3,5,8,16)
RS = ("1/5","1/2","2/3","9/10","99/100","1")
WS = ("1/10","1/2","1","3/2","7")
POLYNOMIAL_N, ENUMERATION_N, TRANSFORM_N = 16,8,50
CURRENT_PHASE = "preflight"


class CheckFailure(Exception):
    """Exact equality, inequality, inventory, or schema failure."""


def require(test, message):
    if not test:
        raise CheckFailure(message)


def equal(left, right, label):
    require(left == right, label+": exact mismatch")


def keys(obj, expected, context):
    require(type(obj) is dict, context+": expected object")
    equal(set(obj),set(expected),context+": missing/extra keys")


def integer(value, context):
    require(type(value) is int,context+": expected integer, not bool/float")
    return value


def rational(value, context):
    require(type(value) is str and re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?",value) is not None,
            context+": expected canonical rational string")
    answer=F(value)
    equal(str(answer),value,context+": noncanonical rational")
    return answer


def vector(value, length, context):
    require(type(value) is list,context+": expected list")
    equal(len(value),length,context+": wrong length")
    return [rational(x,context+"["+str(i)+"]") for i,x in enumerate(value)]


def reject_number(value):
    raise CheckFailure("noninteger JSON number forbidden: "+value)


def unique_object(pairs):
    result={}
    for key,value in pairs:
        require(key not in result,"duplicate JSON key: "+key)
        result[key]=value
    return result


def load_json(path):
    raw=path.read_bytes()
    require(len(raw)<=4_000_000,"JSON input exceeds 4 MB limit")
    return raw,json.loads(raw.decode("utf-8"),object_pairs_hook=unique_object,
                          parse_float=reject_number,parse_constant=reject_number)


def schema(data):
    keys(data,("schema","scope","inventory","frozen_cases","level_polynomials","zero_level"),"fixtures")
    equal(data["schema"],"report107-exact-weighted-levels-v1","schema")
    equal(data["scope"],"Finite integer/rational checks only; no asymptotic claim is certified.","scope")
    expected={"M":list(MS),"r":list(RS),"w":list(WS),"moment_orders":[1,2,3,4],
              "zeta":["0","1/3","1"],"polynomial_max_n":POLYNOMIAL_N,
              "enumeration_max_n":ENUMERATION_N,"zero_transform_max_n":TRANSFORM_N}
    keys(data["inventory"],expected,"inventory")
    equal(data["inventory"],expected,"fixed complete inventory")
    # Type checks also exclude bools, which Python normally compares equal to ints.
    for name in ("M","moment_orders"):
        for x in data["inventory"][name]:
            integer(x,"inventory."+name)
    for name in ("polynomial_max_n","enumeration_max_n","zero_transform_max_n"):
        integer(data["inventory"][name],"inventory."+name)
    require(type(data["frozen_cases"]) is list,"cases must be a list")
    equal(len(data["frozen_cases"]),len(MS)*len(RS),"complete frozen cases")
    for case,(M,rt) in zip(data["frozen_cases"],product(MS,RS)):
        keys(case,("M","r","q","scaled_interpretation","v","lambda","t","f","p",
                   "b_scaled","c_scaled","h_scaled","actual_q0_b_c_h_zero","weights"),"case")
        equal(integer(case["M"],"M"),M,"ordered M inventory")
        equal(case["r"],rt,"ordered r inventory")
        endpoint=rt=="1"
        equal(case["q"],"0" if endpoint else "-M log r (symbolic)","symbolic q")
        equal(case["scaled_interpretation"],"continuous_limit_at_q=0" if endpoint else "divided_by_q","normalized interpretation")
        require(type(case["actual_q0_b_c_h_zero"]) is bool,"endpoint flag type")
        equal(case["actual_q0_b_c_h_zero"],endpoint,"actual q=0 flag")
        require(type(case["weights"]) is list,"weights must be a list")
        equal(len(case["weights"]),len(WS),"complete weighted cases")
        for wc,wt in zip(case["weights"],WS):
            keys(wc,("w","lambda_w","d_w","delta_w","p_w","scaled_first_moment",
                     "increment_moments","tracker_drift"),"weighted case")
            equal(wc["w"],wt,"ordered weight inventory")
    keys(data["zero_level"],("fishburn","primitive","inverse_transform_rows"),"zero-level fixture")


def frozen_checks(cases):
    counts=Counter()
    def check(label,test,context):
        require(test,label+"; "+context)
        counts[label]+=1
    for case in cases:
        M,r=case["M"],F(case["r"])
        context="M="+str(M)+", r="+str(r)
        v,lam,t=[rational(case[k],context+" "+k) for k in ("v","lambda","t")]
        f,p,b,h=[vector(case[k],M+(k=="h_scaled"),context+" "+k)
                   for k in ("f","p","b_scaled","h_scaled")]
        c=rational(case["c_scaled"],context+" c_scaled")
        check("rational_parametrization",0<r<=1 and v==r**(-M) and f==[r**l for l in range(M)],context)
        check("unweighted_positive_parameters",v>=1 and lam>0 and all(x>0 for x in f+p),context)
        check("unweighted_eigenvalue_formula",lam==(F(M) if r==1 else (v-1)/(1-r)),context)
        check("diagonal_parameter",t==v/lam==p[0] and 0<t<=1,context)
        if r==1:
            check("q0_unweighted_kernel",v==1 and lam==M and f==[F(1)]*M and p==[F(1,M)]*M,context)
        else:
            check("geometric_kernel",p==[(1-r)*r**d/(1-r**M) for d in range(M)],context)
        P=[[p[(j-l)%M] for j in range(M)] for l in range(M)]
        direct_b=[]
        for l in range(M):
            check("unweighted_eigen_rows",sum((v if j>=l else 1)*f[j] for j in range(M))==lam*f[l],context+", l="+str(l))
            check("unweighted_stochastic_rows",sum(P[l])==1,context)
            for j in range(M):
                check("unweighted_doob_entries",P[l][j]==(v if j>=l else 1)*f[j]/(lam*f[l]),context)
            direct_b.append(sum(P[l][j]*int(j>=l)*F(j,M) for j in range(M)))
        for j in range(M):
            check("unweighted_stationary_columns",sum(P[l][j] for l in range(M))==1,context)
        for l in range(M):
            check("normalized_b_finite_sums",b[l]==direct_b[l],context+", l="+str(l))
        check("normalized_c_stationary_mean",c==sum(direct_b)/M,context)
        check("normalized_c_bounds",0<=c<=F(M-1,2*M)<=F(1,2),context)
        ew=sum(p[d]*F(d,M) for d in range(M))
        ew2=sum(p[d]*F(d,M)**2 for d in range(M))
        mean_formula=F(M-1,2*M) if r==1 else r/(M*(1-r))-r**M/(1-r**M)
        check("geometric_mean",ew==mean_formula,context)
        check("c_circular_moment_identity",c==(1-ew2)/2-(1-ew)/(2*M),context)
        if r==1:
            A,J=F(1,2),-F(M-1,2*M)
            check("q0_normalized_b_limit",b==[F(M*(M-1)-l*(l-1),2*M*M) for l in range(M)],context)
            check("q0_normalized_c_limit",c==F(M*M-1,3*M*M),context)
        else:
            A=M*(1/r-1)/(2*(1-r**M))
            J=r**M/(1-r**M)-r/(M*(1-r))
        for l in range(M+1):
            x=F(l,M)
            check("normalized_corrector_stable_formula",h[l]==A*x*(1-x)+J*x,context+", l="+str(l))
        check("normalized_corrector_seam",h[0]==0 and h[M]-h[0]==J<=0,context)
        for l in range(M):
            check("unweighted_poisson_rows",sum(P[l][j]*h[j] for j in range(M))-h[l]==c-b[l],context)
        increments=[]
        for l in range(M):
            row=[]
            for j in range(M):
                a=int(j>=l)
                inc=F(a)-F(j,M+a)+F(l,M)
                check("tracker_transition_identity",inc==1-F((j-l)%M,M)+F(a*j,M*(M+a)),context)
                check("tracker_increment_bounds",0<=inc<=2,context)
                row.append(inc)
            increments.append(row)
        for wc in case["weights"]:
            w=F(wc["w"])
            cx=context+", w="+str(w)
            lamw,dw,delta=[rational(wc[k],cx+" "+k) for k in ("lambda_w","d_w","delta_w")]
            pw=vector(wc["p_w"],M,cx+" p_w")
            first=vector(wc["scaled_first_moment"],M,cx+" scaled_first_moment")
            moments=vector(wc["increment_moments"],4,cx+" increment_moments")
            drifts=vector(wc["tracker_drift"],M,cx+" tracker_drift")
            check("weighted_eigenvalue_shift",lamw==lam+(w-1)*v and lamw>0,cx)
            check("weighted_denominator",dw==lamw/lam==1+(w-1)*t and dw>=min(F(1),w)>0,cx)
            check("signed_delta_formula",delta==(w-1)*t/dw and 1-delta==1/dw,cx)
            check("signed_delta_regime",(delta<0 if w<1 else delta==0 if w==1 else 0<delta<1),cx)
            counts["weighted_cases_below_one" if w<1 else "weighted_cases_at_one" if w==1 else "weighted_cases_above_one"]+=1
            check("weighted_strict_positivity",all(x>0 for x in pw),cx)
            if r==1:
                check("q0_weighted_eigenvalue",lamw==M+w-1,cx)
                check("q0_weighted_entries",pw==[(w if d==0 else 1)/(M+w-1) for d in range(M)],cx)
                check("q0_increment_mean",sum(pw[d]*F(d,M) for d in range(M))==F(M-1,2)/(M+w-1),cx)
            Pw=[[pw[(j-l)%M] for j in range(M)] for l in range(M)]
            for l in range(M):
                check("weighted_eigen_rows",sum((v if j>=l else 1)*(w if j==l else 1)*f[j] for j in range(M))==lamw*f[l],cx)
                check("weighted_stochastic_rows",sum(Pw[l])==1,cx)
                for j in range(M):
                    check("weighted_doob_entries",Pw[l][j]==(v if j>=l else 1)*(w if j==l else 1)*f[j]/(lamw*f[l]),cx)
                    check("signed_algebraic_mixture_entries",Pw[l][j]==(1-delta)*P[l][j]+delta*int(j==l),cx)
                    check("weighted_entry_ratio",Pw[l][j]==P[l][j]*(w if j==l else 1)/dw,cx)
                ph_difference=sum(Pw[l][j]*(h[j]-h[l]) for j in range(M))
                check("weighted_poisson_operator_rows",ph_difference==(c-b[l])/dw,cx)
                for zeta in (F(0),F(1,3),F(1)):
                    actual=sum(Pw[l][j]*(int(j>=l)*F(j,M)+zeta*(h[j]-h[l])) for j in range(M))
                    old=(1-zeta)*b[l]+zeta*c
                    check("weighted_corrector_first_moments",actual==old+delta*(F(l,M)-old),cx)
                    if zeta==1:
                        check("weighted_first_moment_fixture",actual==first[l],cx)
                actual_drift=sum(Pw[l][j]*increments[l][j] for j in range(M))
                old_drift=sum(P[l][j]*increments[l][j] for j in range(M))
                check("weighted_tracker_drift",actual_drift==old_drift/dw+delta*(1+F(l,M*(M+1)))==drifts[l],cx)
                if r==1:
                    # These are ACTUAL q=0 values; no division by zero is performed.
                    actual_b=actual_c=F(0)
                    actual_h=[F(0)]*M
                    actual_z=sum(Pw[l][j]*(0*int(j>=l)*F(j,M)+actual_h[j]-actual_h[l]) for j in range(M))
                    check("q0_actual_zero_corrector",actual_z==actual_c+delta*(0*F(l,M)-actual_c)==actual_b==0,cx)
            for j in range(M):
                check("weighted_stationary_columns",sum(Pw[l][j] for l in range(M))==1,cx)
            for k in range(1,5):
                actual=sum(pw[d]*F(d,M)**k for d in range(M))
                check("weighted_increment_moments",actual==sum(p[d]*F(d,M)**k for d in range(M))/dw==moments[k-1],cx)
        counts["frozen_cases"]+=1
        counts["q0_cases" if r==1 else "positive_q_cases"]+=1
    return dict(sorted(counts.items()))


def incoming_level_polynomials():
    """Independent incoming-state recurrence; no outgoing (K,L,E) transitions."""
    layer={(0,0):[1]}
    polys=[[1],[1]]
    for n in range(2,POLYNOMIAL_N+1):
        nxt={}
        poly=[0]*n
        for K in range(n):
            for j in range(K+1):
                coeff=[0]*n
                # Non-ascent arrivals: old count K and old last L>j.
                for L in range(j+1,K+1):
                    for e,value in enumerate(layer.get((K,L),())):
                        coeff[e]+=value
                # Strict-ascent arrivals: old count K-1 and old last L<j.
                for L in range(j):
                    for e,value in enumerate(layer.get((K-1,L),())):
                        coeff[e]+=value
                # Equality arrival is a weak ascent and adds one level.
                for e,value in enumerate(layer.get((K-1,j),())):
                    coeff[e+1]+=value
                if any(coeff):
                    require(2*n<=(K+1)*(K+2),"deterministic reachable-state support")
                    nxt[K,j]=coeff
                for e,value in enumerate(coeff):
                    poly[e]+=value
        layer=nxt
        polys.append(poly)
    return polys


def inversion_enumeration(n):
    """Filter all n! inversion sequences; rescan every prefix from the definition."""
    if n==0:
        return [1]
    coeff=[0]*n
    for seq in product(*(range(i) for i in range(1,n+1))):
        if all(seq[i]<=1+sum(seq[t+1]>=seq[t] for t in range(i-1)) for i in range(1,n)):
            coeff[sum(seq[t+1]==seq[t] for t in range(n-1))]+=1
    return coeff


def polynomial_checks(stored):
    require(type(stored) is list,"polynomials must be list")
    equal(len(stored),POLYNOMIAL_N+1,"complete polynomial length inventory")
    generated=incoming_level_polynomials()
    for n,(actual,expected) in enumerate(zip(stored,generated)):
        require(type(actual) is list,"coefficient vector must be list")
        for value in actual:
            require(integer(value,"level coefficient")>=0,"negative level coefficient")
        equal(actual,expected,"incoming transition polynomial n="+str(n))
    for n in range(ENUMERATION_N+1):
        equal(stored[n],inversion_enumeration(n),"independent inversion enumeration n="+str(n))
    initial=[[1],[1],[1,1],[2,3,1],[5,11,6,1]]
    equal(stored[:len(initial)],initial,"published initial polynomial coefficients")
    evaluated=0
    # A second direct weighted state recurrence tests rational evaluations and the
    # exact finite change-of-weight MGF ratio without evaluating an exponential.
    for wt in WS:
        w=F(wt)
        layer={(0,0):F(1)}
        for n in range(1,POLYNOMIAL_N+1):
            value=sum(layer.values())
            equal(value,sum(F(c)*w**e for e,c in enumerate(stored[n])),"weighted transition evaluation")
            for s in (F(1,2),F(3,2)):
                numerator=sum(F(c)*(w*s)**e for e,c in enumerate(stored[n]))
                mgf=sum(F(c)*w**e/value*s**e for e,c in enumerate(stored[n]))
                equal(mgf,numerator/value,"finite exact change-of-weight identity")
            evaluated+=1
            if n<POLYNOMIAL_N:
                nxt={}
                for (K,L),mass in layer.items():
                    for j in range(K+2):
                        key=(K+int(j>=L),j)
                        nxt[key]=nxt.get(key,F(0))+mass*(w if j==L else 1)
                layer=nxt
    return {"transition_polynomials":len(generated),"independent_enumeration_lengths":ENUMERATION_N+1,
            "rational_weighted_polynomial_evaluations":evaluated,
            "finite_change_of_weight_identities":2*evaluated}


def ordinary_prefix_counts(allow_equal):
    """Positive incoming prefix/suffix recurrence for strict ascents."""
    rows=[[1]]
    totals=[1,1]
    for n in range(1,TRANSFORM_N):
        prefix=[]
        for row in rows:
            sums=[0]
            for x in row:
                sums.append(sums[-1]+x)
            prefix.append(sums)
        new=[]
        for K in range(n+1):
            row=[]
            for j in range(K+1):
                first=0
                if K<len(rows):
                    cut=min(j+int(not allow_equal),len(rows[K]))
                    first=prefix[K][-1]-prefix[K][cut]
                second=prefix[K-1][min(j,len(rows[K-1]))] if K>0 else 0
                row.append(first+second)
            new.append(row)
        rows=new
        totals.append(sum(map(sum,rows)))
    return totals


def zero_checks(data,polys):
    fishburn,primitive=data["fishburn"],data["primitive"]
    for name,arr in (("fishburn",fishburn),("primitive",primitive)):
        require(type(arr) is list,"zero-level counts must be lists")
        equal(len(arr),TRANSFORM_N+1,"complete zero-level count range")
        for value in arr:
            require(integer(value,name)>0,"nonpositive zero-level count")
    equal(fishburn,ordinary_prefix_counts(True),"ordinary Fishburn prefix recurrence")
    equal(primitive,ordinary_prefix_counts(False),"primitive ascent prefix recurrence")
    equal(fishburn[:11],[1,1,2,5,15,53,217,1014,5335,31240,201608],"Fishburn initial values")
    equal(primitive[:11],[1,1,1,2,5,16,61,271,1372,7795,49093],"primitive initial values")
    rows=data["inverse_transform_rows"]
    require(type(rows) is list,"inverse rows must be list")
    equal(len(rows),TRANSFORM_N,"complete inverse-transform inventory")
    entries=0
    for n in range(1,TRANSFORM_N+1):
        row=rows[n-1]
        require(type(row) is list,"inverse row must be list")
        equal(len(row),n,"inverse transform ends at n-1")
        for j,value in enumerate(row):
            integer(value,"inverse transform summand")
            equal(value,(-1)**j*comb(n-1,j)*fishburn[n-j],"inverse binomial summand n="+str(n)+", j="+str(j))
            entries+=1
        equal(sum(row),primitive[n],"inverse zero-level transform")
        equal(sum(comb(n-1,m-1)*primitive[m] for m in range(1,n+1)),fishburn[n],"forward run-length transform")
    for n,poly in enumerate(polys):
        equal(poly[0],primitive[n],"weak zero-level constant coefficient n="+str(n))
    return {"fishburn_recurrence_values":len(fishburn),"primitive_recurrence_values":len(primitive),
            "inverse_transform_summands":entries,"inverse_zero_level_transforms":TRANSFORM_N,
            "forward_run_length_transforms":TRANSFORM_N,"zero_level_polynomial_constant_terms":len(polys)}


def run(fixtures_path):
    global CURRENT_PHASE
    CURRENT_PHASE="preflight"
    raw,data=load_json(fixtures_path)
    schema(data)
    CURRENT_PHASE="frozen_exact_algebra"
    result={"status":"passed","arithmetic":"integers_and_exact_rationals_only",
            "scope":"Finite checks only; no analytic theorem, limit, or uniform error bound is certified.",
            "fixture_sha256":sha256(raw).hexdigest(),"frozen":frozen_checks(data["frozen_cases"])}
    CURRENT_PHASE="transition_polynomials"
    result["polynomials"]=polynomial_checks(data["level_polynomials"])
    CURRENT_PHASE="zero_level_transform"
    result["zero_level"]=zero_checks(data["zero_level"],data["level_polynomials"])
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures",type=Path,default=HERE/"fixtures.json")
    parser.add_argument("--expected-summary",type=Path,default=HERE/"expected_summary.json")
    args=parser.parse_args()
    try:
        result=run(args.fixtures)
        global CURRENT_PHASE
        CURRENT_PHASE="expected_summary"
        _,expected=load_json(args.expected_summary)
        equal(result,expected,"committed expected summary")
    except Exception as error:
        print(json.dumps({"status":"failed","phase":CURRENT_PHASE,"error_type":type(error).__name__,
                          "error":str(error),"python_optimization":sys.flags.optimize},sort_keys=True),file=sys.stderr)
        return 1
    print(json.dumps({**result,"python_optimization":sys.flags.optimize},sort_keys=True))
    return 0


if __name__=="__main__":
    sys.exit(main())
