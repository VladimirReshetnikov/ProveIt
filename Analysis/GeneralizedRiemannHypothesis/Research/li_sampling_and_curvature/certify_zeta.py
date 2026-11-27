#!/usr/bin/env python3
"""Interval certificate for polynomially sampled second differences of the Riemann Li coefficients.

Run: python3 certify_zeta.py
Dependencies: MPFI and MPFR shared libraries on a 64-bit GNU/Linux system.
All assertions must be enabled (the script refuses Python -O).
"""
import ctypes as C
from ctypes.util import find_library
from fractions import Fraction
from math import comb, factorial

if not __debug__:
    raise RuntimeError("Enable assertions by running Python without -O.")

mpfi = C.CDLL(find_library("mpfi") or "libmpfi.so.0")
mpfr = C.CDLL(find_library("mpfr") or "libmpfr.so.6")
PREC = 192
P = C.c_void_p


# Standard MPFR/MPFI C memory layouts on the GNU/Linux LP64 ABI.
class Real(C.Structure):
    _fields_ = [("prec", C.c_long), ("sign", C.c_int), ("exp", C.c_long),
                ("limbs", C.POINTER(C.c_ulong))]


class IntervalData(C.Structure):
    _fields_ = [("left", Real), ("right", Real)]


def bind(lib, name, result, args):
    fn = getattr(lib, name)
    fn.argtypes = args
    fn.restype = result
    return fn


init = bind(mpfi, "mpfi_init2", None, [P, C.c_long])
clear = bind(mpfi, "mpfi_clear", None, [P])
set_str = bind(mpfi, "mpfi_set_str", C.c_int, [P, C.c_char_p, C.c_int])
cmp_fr = bind(mpfr, "mpfr_cmp", C.c_int, [P, P])
nan_fr = bind(mpfr, "mpfr_nan_p", C.c_int, [P])
binary = {name: bind(mpfi, "mpfi_" + name, C.c_int, [P, P, P])
          for name in ("add", "sub", "mul", "div", "union")}
unary = {name: bind(mpfi, "mpfi_" + name, C.c_int, [P, P])
         for name in ("abs", "log", "exp", "neg", "sin", "cos", "atan")}
constants = {name: bind(mpfi, "mpfi_const_" + name, C.c_int, [P])
             for name in ("pi", "euler")}


class I:
    def __init__(self, value=None):
        self.data = IntervalData()
        self.p = C.byref(self.data)
        init(self.p, PREC)
        if value is not None:
            assert set_str(self.p, str(value).encode("ascii"), 10) == 0

    def __del__(self):
        clear(self.p)

    @staticmethod
    def wrap(x):
        return x if isinstance(x, I) else I(x)

    def unary(self, name):
        v = I()
        unary[name](v.p, self.p)
        return v

    def binary(self, name, x):
        x, v = I.wrap(x), I()
        binary[name](v.p, self.p, x.p)
        return v

    def __add__(self, x): return self.binary("add", x)
    __radd__ = __add__
    def __sub__(self, x): return self.binary("sub", x)
    def __rsub__(self, x): return I.wrap(x) - self
    def __mul__(self, x): return self.binary("mul", x)
    __rmul__ = __mul__
    def __truediv__(self, x): return self.binary("div", x)
    def __neg__(self): return self.unary("neg")

    def strictly_below(self, x):
        x = I.wrap(x)
        a, b = C.byref(self.data.right), C.byref(x.data.left)
        return not (nan_fr(a) or nan_fr(b)) and cmp_fr(a, b) < 0


def const(name):
    v = I()
    constants[name](v.p)
    return v


def add(z, w): return (z[0]+w[0], z[1]+w[1])
def sub(z, w): return (z[0]-w[0], z[1]-w[1])
def scale(c, z): return (c*z[0], c*z[1])


def mul(z, w):
    a,b = z
    c,d = w
    return (a*c-b*d, a*d+b*c)


def inv(z):
    a,b = z
    norm = a*a+b*b
    return (a/norm, -b/norm)


# Euler-Maclaurin with 20 Bernoulli corrections at N=256.
N, M = 256, 20
b = [Fraction(1)]
for j in range(1, 2*M+1):
    b.append(-sum(comb(j+1,k)*b[k] for k in range(j))/(j+1))
assert b[2] == Fraction(1,6) and b[4] == Fraction(-1,30)
coeffs = []
for k in range(1, M+1):
    c = b[2*k]/(factorial(2*k)*N**(2*k-1))
    coeffs.append(I(c.numerator)/c.denominator)
logs = [I(n).unary("log") for n in range(1, N+1)]
# Bound 2*zeta(40)/(2*pi)^40 < 4/6^40, |(s)_40| < 171^40,
# N^(1-sigma-40) <= N^(1-40); discard the denominator sigma+39>1.
assert 4*N*Fraction(171,6*N)**40 < Fraction(1,10**34)
error = I("-1e-34").binary("union", I("1e-34"))


def zeta(sigma, t):
    assert I("0.49").strictly_below(sigma) and sigma.strictly_below("0.51")
    assert I(13).strictly_below(t) and t.strictly_below(130)
    s = sigma,t
    partial = (I(0),I(0))
    for j,ln in enumerate(logs, start=1):
        magnitude = (-sigma*ln).unary("exp")
        phase = -t*ln
        n_minus_s = (magnitude*phase.unary("cos"), magnitude*phase.unary("sin"))
        if j != N:
            partial = add(partial,n_minus_s)
    corrections = add((I("0.5"),I(0)), scale(N, inv((sigma-1,t))))
    rising = s
    for k,c in enumerate(coeffs, start=1):
        corrections = add(corrections, scale(c, rising))
        if k < M:
            rising = mul(mul(rising, (sigma+2*k-1,t)), (sigma+2*k,t))
    return add(add(partial, mul(n_minus_s, corrections)), (error,error))


# Untrusted rational centers; all forty are checked below.
HEIGHTS = """
14.13472514173469379045725198356247
21.0220396387715549926284795938969
25.01085758014568876321379099256282
30.42487612585951321031189753058409
32.9350615877391896906623689640749
37.58617815882567125721776348070533
40.91871901214749518739812691463325
43.32707328091499951949612216540681
48.00515088116715972794247274942752
49.77383247767230218191678467856372
52.97032147771446064414729660888099
56.44624769706339480436775947670613
59.34704400260235307965364867499222
60.831778524609809844259901824524
65.11254404808160666087505425318371
67.07981052949417371447882889652222
69.54640171117397925292685752655474
72.06715767448190758252210796982617
75.70469069908393316832691676203035
77.14484006887480537268266485630464
79.33737502024936792276359287711623
82.91038085408603018316483749477061
84.73549298051705010573531120682774
87.42527461312522940653166785091921
88.80911120763446542368234807950938
92.49189927055848429625972524181068
94.65134404051988696659792581520815
95.87063422824530975874102921924678
98.83119421819369223332442013862233
101.3178510057313912287854479402923
103.7255380404783394163984081086953
105.4466230523260944936708324141118
107.1686111842764075151233519630862
111.0295355431696745246564503099444
111.8746591769926370856120787167706
114.3202209154527127658909372761911
116.2266803208575543821608043120648
118.7907828659762173229791397026998
121.3701250024206459189455329704999
122.94682929355258820081746033077
""".split()


def certify_heights():
    half, delta, radius = I("0.5"), I("1e-6"), I("1e-18")
    heights = []
    previous = I(0)
    for center in HEIGHTS:
        t = I(center)
        lo, hi = t-radius, t+radius
        assert previous.strictly_below(lo)
        previous = hi
        z0, z1 = zeta(half,t), zeta(half+delta,t)
        assert all(a.unary("abs").strictly_below("1e-25") for a in z0)
        slope = sub(z1,z0)
        assert any(I("0.1").strictly_below((a/delta).unary("abs")) for a in slope)
        # For |s-(1/2+it)|<=1/4, first-order Euler summation from N=1 gives
        # |zeta(s)| <= 1/|s-1| + 1/2 + |s|/(2 Re(s)) < 300 (13<t<130).
        # The Taylor terms of degree >=2 in |h|<=1e-6 have modulus
        # <= 300*(4|h|)^2/(1-4|h|) < 5000 |h|^2.  Therefore
        # |zeta'(s0)|>0.1-5000e-6>0.09.  On |h|=1e-18, the constant
        # term (modulus <2e-25) and higher terms sum to <0.09e-18.
        # Rouche gives one zero in this disc. Distinct discs are disjoint.
        heights.append(lo.binary("union", hi))
    assert len(heights) == 40
    return heights


def check():
    heights = certify_heights()
    total_mass = 2 + const("euler") - (4*const("pi")).unary("log")
    weights = [I(2)/(I("0.25")+t*t) for t in heights]
    phases = [2*(I("0.5")/t).unary("atan") for t in heights]
    missing_mass = total_mass - sum(weights,I(0))
    assert I("0.01022325").strictly_below(missing_mass)
    assert missing_mass.strictly_below("0.01022326")
    print("Certified one zeta zero in each of 40 disjoint discs of radius 1e-18.")
    print("Remaining spectral mass is in (0.01022325, 0.01022326).")
    for n,lower,upper in [(891327,"0.01161996","0.03206648"),
                          (891327**2,"0.01387458","0.03432110")]:
        partial = sum((w*(n*theta).unary("cos") for w,theta in zip(weights,phases)),I(0))
        # On RH every unseen term has modulus at most its positive mass.
        assert I(lower).strictly_below(partial - missing_mass)
        assert (partial + missing_mass).strictly_below(upper)
        print(f"{lower} < curvature({n}) < {upper}")
    # Decimal lower bounds in the manuscript table are exact rationals.
    cases = [(891327,(1,1),("0.01161","0.01387")),
             (842728,(1,-1),("0.01180","0.01349")),
             (602346,(-1,1),("0.01165","0.01133")),
             (673696,(-1,-1),("0.01119","0.01148"))]
    for seed, signs, bounds in cases:
        for n, sign, bound in zip((seed,seed*seed),signs,bounds):
            signed_sum = sum((sign*w*(n*theta).unary("cos")
                              for w,theta in zip(weights,phases)), I(0))
            assert I(bound).strictly_below(signed_sum-missing_mass)
        a,b = signs
        print(f"h={seed}: {a:+}*curvature(h) > {bounds[0]}, "
              f"{b:+}*curvature(h^2) > {bounds[1]}")


if __name__ == "__main__":
    check()
