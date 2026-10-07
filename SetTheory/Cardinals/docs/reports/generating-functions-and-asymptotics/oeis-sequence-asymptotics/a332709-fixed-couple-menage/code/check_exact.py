"""Deterministic exact tests. Works unchanged with python -O."""
from fractions import Fraction as Q
from itertools import permutations
from math import comb, factorial
import json
import sys
from hashlib import sha256
import menage as m

checks = 0

def ensure(ok, label):
    global checks
    if not ok:
        raise RuntimeError(label)
    checks += 1


def rejects(fn, exception, label):
    try:
        fn()
    except exception:
        return label
    raise RuntimeError("negative control not detected: "+label)


def permanent_cofactor(n, s):
    full = (1<<n)-1
    dp = {1<<(s+1): 1}
    for row in range(1,n):
        allowed = full ^ ((1<<row)|(1<<((row+1)%n)))
        nxt = {}
        for used, count in dp.items():
            bits = allowed & ~used
            while bits:
                bit = bits & -bits
                bits -= bit
                nxt[used|bit] = nxt.get(used|bit,0)+count
        dp = nxt
    return dp.get(full,0)


def polynomial_checks():
    previous, current = (1,), (1,1)
    ensure(m.path_rooks(0)==previous, "R0")
    ensure(m.path_rooks(1)==current, "R1")
    for edges in range(2,101):
        new = [0]*max(len(current), len(previous)+1)
        for j,c in enumerate(current): new[j] += c
        for j,c in enumerate(previous): new[j+1] += c
        ensure(tuple(new)==m.path_rooks(edges), f"R recurrence {edges}")
        previous,current = current,tuple(new)
    for a in range(30):
        for b in range(a+2,61):
            p = m._product(m.path_rooks(a+2),m.path_rooks(b))
            q = m._product(m.path_rooks(a),m.path_rooks(b+2))
            lhs = [0]*max(len(p),len(q))
            for j,v in enumerate(p): lhs[j] += v
            for j,v in enumerate(q): lhs[j] -= v
            rhs = [0]*(a+2)+[(-1)**(a+2)*v for v in m.path_rooks(b-a-2)]
            lhs += [0]*(len(rhs)-len(lhs)); rhs += [0]*(len(lhs)-len(rhs))
            ensure(lhs==rhs, f"polynomial identity {a},{b}")


def count_checks():
    for n in range(3,101):
        row = [m.fixed_count(n,s) for s in range(1,n-1)]
        u = m.circular_count(n); h=(n-1)//2
        ensure(sum(row)==u, f"row sum {n}")
        ensure(row==row[::-1], f"reflection {n}")
        ensure(min(row)>0, f"positivity {n}")
        center_correction = 2*sum(j*m.line_count(n-2*j-2) for j in range(1,h))
        for s,a in enumerate(row,1):
            q = min(s,n-1-s)
            ensure((n-2)*a == u+center_correction-(n-2)*sum(m.line_count(n-2*j-2) for j in range(q,h)),f"mean {n},{s}")
            if s>=2:
                ensure(a-row[s-2]==m.adjacent_difference(n,s+2),f"difference {n},{s}")
            if 1<s<n-2:
                left,right=row[s-2],row[s]
                ensure(2*a>=left+right,f"concavity {n},{s}")
                ensure(a*a>=left*right,f"log concavity {n},{s}")
                equal_concave = ((n%2 and s in ((n-3)//2,(n+1)//2)) or
                                 (n%2==0 and s in (n//2-1,n//2)))
                equal_log = n%2==0 and s in (n//2-1,n//2)
                ensure((2*a==left+right)==bool(equal_concave), f"concavity equality {n},{s}")
                ensure((a*a==left*right)==equal_log, f"log equality {n},{s}")
        max_positions=[s for s,a in enumerate(row,1) if a==max(row)]
        expected = [(n-1)//2] if n%2 else ([1,2] if n==4 else list(range(n//2-2,n//2+2)))
        ensure(max_positions==expected,f"maxima {n}")
        below=[s for s,a in enumerate(row,1) if (n-2)*a<u]
        above=[s for s,a in enumerate(row,1) if (n-2)*a>u]
        ensure(below==([] if n in (3,4,6) else [1,n-2]),f"exact deficient positions {n}")
        ensure(above==([] if n in (3,4,6) else list(range(2,n-2))),f"exact excess positions {n}")
        ensure(m.exact_total_variation(n)==2*(Q(1,n-2)-Q(row[0],u)),f"exact TV {n}")
        if n>=9:
            ensure((n-2)*row[1]-u>=2*(n-6)**2*m.line_count(n-6)>0,f"q2 lower bound {n}")
    for n in range(3,15):
        for s in range(1,n-1):
            ensure(permanent_cofactor(n,s)==m.fixed_count(n,s), f"independent DP {n},{s}")
    for q in range(1,151):
        coefficient = sum((-1)**(q-r)*factorial(r)*comb(q+r-1,q-r) for r in range(1,q+1))
        ensure(m.line_count(q)==coefficient,f"A127548 OGF {q}")
        ensure(m.line_count(q)==m.circular_count(q)+2*sum(m.circular_count(r) for r in range(q)),f"L U {q}")
        ensure(m.line_count(q+2)>=m.line_count(q),f"injection inequality {q}")
        ensure((m.line_count(q+2)==m.line_count(q))==(q==1),f"injection equality {q}")
        ensure(sum(m.line_count(r) for r in range(q%2 or 2,q+1,2))<=2*m.line_count(q),f"parity tail {q}")
        if q>=2:
            ensure(m.line_count(q+1)>=q*m.line_count(q),f"growth {q}")
        if q>=3:
            ensure(m.line_count(q)==q*m.line_count(q-1)-m.circular_count(q-2),f"line recurrence {q}")
            ensure(m.circular_count(q-1)<=m.line_count(q),f"append inequality {q}")
    for q in range(1,9):
        admissible = [p for p in permutations(range(1,q+1)) if all(p[i] not in (i+1,i+2) for i in range(q-1))]
        ensure(len(admissible)==m.line_count(q),f"L enumeration {q}")
        images = set()
        for p in admissible:
            image = p[:q-1]+(q+2,p[q-1],q+1)
            ensure(sorted(image)==list(range(1,q+3)) and all(image[i] not in (i+1,i+2) for i in range(q+1)),f"injection image {q}")
            images.add(image)
        ensure(len(images)==len(admissible),f"injective {q}")
        if q>=3:
            for p in permutations(range(1,q)):
                if all(p[i] not in (i+1,((i+1)%(q-1))+1) for i in range(q-1)):
                    image=p+(q,)
                    ensure(all(image[i] not in (i+1,i+2) for i in range(q-1)),f"append injection {q}")


def series_checks():
    expected={None:[1,0,0,0,2,16,90,456,2296,12052,67238],
              1:[1,0,0,-1,-4,-12,-33,-90,-246,-622,-1067],
              2:[1,0,0,0,2,15,75,311,1136,3629,9077],
              3:[1,0,0,0,2,16,90,455,2268,11583,61099],
              4:[1,0,0,0,2,16,90,456,2296,12051,67193]}
    for q,target in expected.items():
        ensure(m.row_series(10,q)==tuple(target),f"rational coefficients {q}")
        for order in range(11):
            ensure(m.row_series(order,q)==tuple(target[:order+1]),f"order consistency {q},{order}")
    for q in range(1,8):
        order=2*q+1
        delta=[a-b for a,b in zip(m.row_series(order,q),m.row_series(order,None))]
        ensure(delta==[0]*order+[-1],f"boundary first separation {q}")
    ensure(m.tv_series(10)==(0,0,0,0,2,12,48,162,504,1500,4244),"TV coefficients")
    # A different formal route: the exact ordinary-menage recurrence fixes
    # every normalized coefficient from the leading value 1.
    degree=12
    def shift(a,d):
        c=[Q(0)]*(degree+1);c[0]=a[0]
        for r in range(1,degree+1):
            for j in range(degree+1-r): c[r+j]+=a[r]*comb(r+j-1,j)*d**j
        return c
    u=list(m.circular_series(degree))
    shifted=shift(u,1)
    second=m._mul(m._mul([Q(1)]*(degree+1),[Q(2**j) for j in range(degree+1)],degree),shift(u,2),degree)
    residual=[u[k]-shifted[k]-(second[k-2] if k>=2 else 0) for k in range(degree+1)]
    ensure(all(v==0 for v in residual),"independent circular recurrence coefficients")
    l=list(m.line_series(degree))
    rhs=[a+b for a,b in zip(shift(l,1),shift(u,1))]
    ensure(all(l[k]==u[k]+(rhs[k-1] if k else 0) for k in range(degree+1)),"independent L recurrence coefficients")
    ensure(Q(1,8)-Q(1,4)+Q(13,12)==Q(23,24),"inverse coefficient residual")


def main():
    cap_before = sys.get_int_max_str_digits() if hasattr(sys,"get_int_max_str_digits") else None
    polynomial_checks(); count_checks(); series_checks()
    large = m.fixed_count(600,4)
    large_text = m.integer_decimal(large)
    ensure(len(large_text)>640,"large count exceeds minimum digit cap")
    ensure(m.parse_integer_decimal(large_text)==large,"large positive decimal round trip")
    ensure(m.parse_integer_decimal(m.integer_decimal(-large))==-large,"large negative decimal round trip")
    ensure(m.integer_decimal(0)=="0" and m.parse_integer_decimal("0")==0,"zero serialization")
    ensure((sys.get_int_max_str_digits() if hasattr(sys,"get_int_max_str_digits") else None)==cap_before,"caller digit cap preserved")
    wrong = [
        (lambda: ensure(m.circular_count(1)==0,"wrong U1"),RuntimeError,"signed U1"),
        (lambda: ensure(m.adjacent_difference(8,6)==m.line_count(0),"wrong center"),RuntimeError,"center is not L0"),
        (lambda: ensure(m.row_series(10,4)[9]==12052,"wrong fourth column"),RuntimeError,"fourth column x9"),
        (lambda: ensure(m.tv_series(4)[4]==1,"wrong TV"),RuntimeError,"TV coefficient"),
        (lambda: m.fixed_count(5,4),ValueError,"column above domain"),
        (lambda: m.fixed_count(5,0),ValueError,"column below domain"),
        (lambda: m.adjacent_difference(5,3),ValueError,"nonexistent predecessor"),
        (lambda: m.line_count(-1),ValueError,"negative line index"),
        (lambda: m.circular_count(True),TypeError,"boolean index"),
        (lambda: m.path_rooks(2.0),TypeError,"floating index"),
        (lambda: m.row_series(-1,1),ValueError,"negative order"),
        (lambda: m.row_series(3,0),ValueError,"zero distance"),
        (lambda: m.row_series(3,False),TypeError,"boolean distance"),
        (lambda: m.exact_total_variation(2),ValueError,"small distribution domain"),
        (lambda: m.parse_integer_decimal("1e2"),ValueError,"invalid decimal notation"),
        (lambda: m.parse_integer_decimal(""),ValueError,"empty decimal"),
        (lambda: m.integer_decimal(True),TypeError,"boolean decimal value"),
        (lambda: ensure(m.line_count(2)==2*m.line_count(1)-m.circular_count(0),"wrong m2 recurrence"),RuntimeError,"line recurrence small correction"),
        (lambda: ensure(m.exact_total_variation(6)>0,"wrong n6 sign"),RuntimeError,"uniform n6 exception"),
        (lambda: ensure(5*m.fixed_count(7,2)-m.circular_count(7)==2*m.line_count(3)+m.line_count(1),"wrong tail sign"),RuntimeError,"q2 tail sign")]
    negatives=[rejects(*args) for args in wrong]
    out={"passed":True,"exact_checks":checks,
         "large_integer_serialization":{"n":600,"s":4,"decimal_digits":len(large_text),"sha256":sha256(large_text.encode()).hexdigest()},"row_max_n":100,"permanent_max_n":14,
         "line_enumeration_max_m":8,"negative_controls_detected":negatives,
         "rows_3_through_10":[[m.fixed_count(n,s) for s in range(1,n-1)] for n in range(3,11)],
         "ratio_coefficients_through_10":{str(q):[m.fraction_decimal(v) for v in m.row_series(10,q)] for q in (None,1,2,3,4,5)},
         "tv_coefficients_through_10":[m.fraction_decimal(v) for v in m.tv_series(10)]}
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
