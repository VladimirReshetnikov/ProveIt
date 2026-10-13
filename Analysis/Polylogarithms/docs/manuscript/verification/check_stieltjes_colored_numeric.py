"""Independent ordinary quadrature for golden-shift colored moments.

Read-only imports the preserved balanced-kernel evaluator. Its Euler--Maclaurin
and tail expansions are truncated: these are precision/refinement experiments,
not interval certificates. No Mellin formula is used to evaluate the LHS.
Run from any directory with Python, mpmath and sympy installed.
"""
from pathlib import Path
import importlib.util
import json
import sys
from functools import lru_cache
from math import factorial
import mpmath as mp

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / '.git').exists())
sys.dont_write_bytecode = True
SOURCE = ROOT / "Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments/code/balanced.py"
spec = importlib.util.spec_from_file_location("preserved_balanced", SOURCE)
balanced = importlib.util.module_from_spec(spec)
spec.loader.exec_module(balanced)


def euler_at_golden(k, a):
    # E_k(a) = 2/(k+1) [B_(k+1)(a)-2^(k+1) B_(k+1)(a/2)].
    # Known exact vanishing is imposed algebraically, never by a tolerance.
    if k in (4, 5):
        return mp.mpf(0)
    return 2*(mp.bernpoly(k+1,a)-2**(k+1)*mp.bernpoly(k+1,a/2))/(k+1)


def run(dps, n, r, cutoff, tail_order):
    mp.mp.dps = dps
    a = (1+mp.sqrt(5))/2
    T = mp.mpf(cutoff)
    kernels = {q: balanced.Kernel(q,n,r) for q in (4,5)}
    @lru_cache(maxsize=None)
    def colored(q, x):
        return (kernels[q](x/2,a/2)-kernels[q](x/2,(a+1)/2))/2
    def integral(q, m):
        def f(x):
            if not x:
                return mp.mpf(0)
            return x**(m-1)*colored(q,x)
        core = mp.quad(lambda t: 4*t**3*f(t**4), [0,1])
        core += mp.quad(f,[1,8,T])
        tail = mp.mpf(0)
        for k in range(max(q,m),tail_order+1):
            Ak = euler_at_golden(k,a)/2
            coefficient = ((-1)**k*Ak*factorial(q)
                           *balanced.pochhammer_coefficients(k,q)[q]/mp.factorial(k))
            tail += coefficient*T**(m-k-1)/(k+1-m)
        return core+tail, core, tail
    def phi_derivative(s):
        return mp.diff(lambda v: 2**(-v)*(mp.zeta(v,a/2)-mp.zeta(v,(a+1)/2)),s)
    rhs4, rhs5 = phi_derivative(-4), phi_derivative(-5)
    records = []
    vals = {}
    for q,m,rhs in ((4,5,rhs4),(4,6,-3*rhs5),(5,6,-rhs5)):
        lhs,core,tail = integral(q,m)
        vals[q,m]=lhs
        err=abs(lhs-rhs)
        record={"kind":"ordinary_moment", "q":q,"m":m,"lhs":mp.nstr(lhs,dps),
                "rhs":mp.nstr(rhs,dps),"absolute_error":mp.nstr(err,12),
                "core":mp.nstr(core,dps),"tail":mp.nstr(tail,dps)}
        records.append(record)
        print(dps,q,m,mp.nstr(err,8),flush=True)
    records.append({"kind":"vanishing_combination", "formula":"I(4,6)-3 I(5,6)",
                    "absolute_error":mp.nstr(abs(vals[4,6]-3*vals[5,6]),12)})
    # Independent defining Lerch derivatives at a fixed positive x.
    x=mp.mpf(3)/2
    for q in (4,5):
        defining=mp.diff(lambda z: x**z*2**(-1-z)
                        *(mp.zeta(1+z,(x+a)/2)-mp.zeta(1+z,(x+a+1)/2)),
                        mp.mpf(0),q,method="quad",radius=mp.mpf("0.15"))
        records.append({"kind":"kernel_definition", "q":q,"x":"3/2",
                        "absolute_error":mp.nstr(abs(colored(q,x)-defining),12)})
    return {"dps":dps,"em_n":n,"em_r":r,"cutoff":cutoff,
            "tail_order":tail_order,"records":records}


if __name__ == "__main__":
    results=[]
    out=Path(__file__).with_suffix('.json')
    for params in ((55,32,30,64,80),(70,48,40,80,90)):
        results.append(run(*params))
        out.write_text(json.dumps({"evidence":"Uncertified precision-refined quadrature", "runs":results},indent=2)+"\n",encoding="utf-8")
    threshold=mp.mpf("1e-40")
    assert all(mp.mpf(record["absolute_error"]) < threshold
               for result in results for record in result["records"])
    print("PASS: all 12 comparisons below 1e-40",flush=True)
