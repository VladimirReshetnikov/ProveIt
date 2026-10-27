"""Exact arithmetic certificates for a 7-group root and 9-group cached tail.

Uses rational enclosures; no correctness gate depends on floating point.
This is a schedule checker, not an end-to-end tensor-contraction/SAT program.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from verify_heterogeneous_schedule import require, sqrt_bounds, constants, decimal


def add(a, b): return a[0]+b[0], a[1]+b[1]
def mul(a, b): return a[0]*b[0], a[1]*b[1]
def scale(a, b): return a[0]*b, a[1]*b
def divide(a, b):
    require(b[0] > 0, "nonpositive interval denominator")
    return a[0]/b[1], a[1]/b[0]
def radical(a): return sqrt_bounds(a[0])[0], sqrt_bounds(a[1])[1]
def point(a): return F(a), F(a)


def log7_over_log2_bounds(ln2):
    # ln7=3ln2 - 2 atanh(1/15), and atanh uses a positive series.
    x, terms = F(1,15), 80
    lo = 2*sum((x**(2*j+1)/(2*j+1) for j in range(terms)), F(0))
    hi = lo + 2*x**(2*terms+1)/((2*terms+1)*(1-x*x))
    quotient = divide((lo,hi),ln2)
    return F(3)-quotient[1], F(3)-quotient[0]


def main():
    pi,ln2=constants()
    omega=log7_over_log2_bounds(ln2)
    p=omega[0]-2,omega[1]-2
    require(0<p[0]<p[1]<1,"omega-2 range")
    p2=mul(p,p)
    K=divide(mul(pi,sqrt_bounds(F(2))),ln2)
    eta0,eta1,delta=F(89,5000),F(1233,125000),F(7,25)
    total=eta0+eta1/(1-delta)
    require(total==F(63,2000),"total capacity")
    require(7**89<2**250,"root packing cap")
    require(9**63<2**200,"tail packing cap")
    require(F(1,5)+total<1,"fresh-side cap")
    require(F(1,4)<delta,"tail u-growth bootstrap")
    # Pair profiles root (2,2,3), tail (3,3,3).
    a0=scale(sqrt_bounds(F(12)),F(1,7))
    matrix0=scale(radical(add(point(24),scale(p2,F(8)))),F(1,7))
    j0=scale(sqrt_bounds(F(24)),F(1,7))
    bt=scale(radical(add(point(4),scale(p2,F(2)))),F(1,3))
    at,jt=point(F(4,9)),point(F(2,3))
    build0=scale(sqrt_bounds(F(30)),F(1,7))
    buildt=scale(sqrt_bounds(F(42)),F(1,9))
    require(matrix0[1]<build0[0],"root matrix work exceeds table construction")
    b0=build0
    require(buildt[1]<bt[0],"tail table construction exceeds matrix work")
    gamma=divide(point(F(10,9)),sqrt_bounds(F(7)))
    tail_cache=divide(at,(1-gamma[1],1-gamma[0]))
    require(tail_cache[1]<bt[0],"tail cache recurrence not matrix dominated")
    root_unit=divide(K,sqrt_bounds(eta0))
    tail_unit=scale(divide(K,sqrt_bounds(eta1)),F(2,7))
    root_work=mul(b0,root_unit)
    child_work=add(mul(a0,root_unit),mul(bt,tail_unit))
    memory_root=mul(j0,root_unit)
    memory_child=mul(jt,tail_unit)
    require(root_work[1]<child_work[0],"time maximizer is not first tail call")
    require(memory_child[1]<memory_root[0],"memory maximizer is not root")
    require(child_work[1]<38,"eventual time coefficient must be below 38")
    require(memory_root[1]<34,"eventual space coefficient must be below 34")
    require(F(3793010908288,10**11)<child_work[0]<child_work[1]<F(3793010908289,10**11),
            "time decimal enclosure mismatch")
    require(F(3362304092165,10**11)<memory_root[0]<memory_root[1]<F(3362304092167,10**11),
            "space decimal enclosure mismatch")
    # Compare against the fixed-r=8 optimized asym family boundary root term.
    # The root scalar b8 uses pair cardinalities12,12,18; discount12.
    b8=scale(radical(add(point(30),scale(p2,F(12)))),F(1,8))
    old_boundary=mul(mul(K,b8),sqrt_bounds(F(60)))
    require(child_work[1]<old_boundary[0],"does not improve fixed-r8 boundary")
    def shown(x):return {"lower":decimal(x[0], rounding='ROUND_FLOOR'),
                         "upper":decimal(x[1], rounding='ROUND_CEILING')}
    return {
        "status":"passed",
        "scope":"exact local cost, schedule, and recurrence certificates; no SAT timing claim",
        "root_alphabet":7,"tail_alphabet":9,
        "root_blocks":[2,2,3],"tail_blocks":[3,3,3],
        "root_range":str(eta0),"tail_first_range":str(eta1),"tail_range_ratio":str(delta),
        "total_capacity":str(total),
        "power_certificates":{"7^89_lt_2^250":True,"9^63_lt_2^200":True},
        "root_pair_counts":{"incident_group":12,"max_incident_block":30,
                            "max_boundary_block":24,"block_pair_classes":[8,12,12]},
        "tail_pair_counts":{"incident_group":16,"max_incident_block":42,
                            "max_boundary_block":36,"block_pair_classes":[18,18,18]},
        "omega":shown(omega),"root_time":shown(root_work),
        "first_tail_time_with_ancestor_cache":shown(child_work),
        "root_space":shown(memory_root),"first_tail_space":shown(memory_child),
        "tail_cache_ratio":shown(tail_cache),"tail_matrix_coefficient":shown(bt),
        "composed_fixed_r8_boundary_time":shown(old_boundary),
        "eventual_integer_time_coefficient":38,"eventual_integer_space_coefficient":34,
    }


if __name__=="__main__":
    print(json.dumps(main(),indent=2,sort_keys=True))
