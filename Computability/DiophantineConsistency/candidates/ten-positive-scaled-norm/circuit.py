"""Literal division-free circuit of the ten-positive-unknown polynomial N (mu-scaled, centered).

Unknowns (strictly positive integers): j, F, alpha, i, T, w, Y, n, eta, zeta.
Fixed numerals: beta, K0, MC, MF, the whole compact44 tuple (MF already shifted).

Every row is one binary +, - or * (including multiplication by a small numeral).
Numerals and the four fixed ports are free leaves. Names follow PROOF.md:
Ap, Hp, Dp, ap stand for A', H', Delta', a'; e is the index excess k-R-1.
"""

WITNESSES = ["j", "F", "alpha", "i", "T", "w", "Y", "n", "eta", "zeta"]
FIXED = ["beta", "K0", "MC", "MF"]
OUTPUT = "N"


def rows():
    """The literal rows (name, op, left, right), in evaluation order."""
    out = []
    def A(name, x, y): out.append((name, "+", x, y))
    def S(name, x, y): out.append((name, "-", x, y))
    def M(name, x, y): out.append((name, "*", x, y))
    # outer registers
    M("2j", 2, "j");          A("J", "2j", 1)                 # J = 2j+1
    M("bJ", "beta", "J");     A("q", "bJ", 1)                 # q = beta J + 1
    S("qmF", "q", "F");       S("C", "qmF", "alpha")          # C = q - F - alpha
    M("X", "w", "q")                                          # X = w q
    M("E", "X", "Y");         A("a", "E", "Y")                # a = XY + Y
    A("k", "eta", "zeta")                                     # k = eta + zeta
    M("kY", "k", "Y");        A("c", "kY", "eta")             # c = kY + eta
    M("q2", "q", "q");        A("mu", "q2", 1)                # mu = q^2 + 1
    S("qm1", "q", 1)
    # mu-scaled main Pell parameter
    A("a2", "a", 2);          M("Am1", "mu", "a2")            # A'-1 = mu(a+2)
    M("4Am1", 4, "Am1");      S("Hp", "4Am1", 1)              # H' = 4A' - 5 = 4(A'-1) - 1
    A("Ap1", "Am1", 2);       M("Dp", "Am1", "Ap1")           # Delta' = A'^2 - 1 = (A'-1)(A'+1)
    S("ap", "Am1", 1)                                         # a' = A' - 2
    # mu-scaled first Pell radicand
    M("muY", "mu", "Y");      M("muY2", "muY", "muY");  M("V0", "X", "muY2")   # V0 = X mu^2 Y^2
    M("V0k", "V0", "k");      A("V0kk", "V0k", "k")           # V0 k, (V0+1) k
    M("V0k2", "V0k", "V0kk"); A("Dtau", "V0k2", 1)            # Dtau = V0(V0+1)k^2 + 1
    # packed index, its majorant and the index excess
    M("G1", "qm1", "qmF");    A("G", "G1", "alpha")           # G = (q-1)(q-F) + alpha
    S("q2m1", "q2", 1);       M("Gq", "G", "q2m1")
    M("qMF", "q", "MF");      A("MCqMF", "MC", "qMF");  M("RJ", "MCqMF", "J")
    A("R", "Gq", "RJ")                                        # R = G(q^2-1) + (MC+q MF)J
    M("q3", "q2", "q")
    S("kR", "k", "R");        S("e", "kR", 1)                 # e = k - R - 1
    A("K0w", "K0", "w");      M("K0wC", "K0w", "C");    S("Bt", "K0wC", "F")   # Bt = (K0+w)C - F
    # strong Pell ordinate and radicand
    M("c2", "c", "c");        M("muc2", "mu", "c2");    M("I", "i", "muc2")    # I = i mu c^2
    M("I2", "I", "I");        M("DpI2", "Dp", "I2");    A("Df", "DpI2", 1)     # Df = 1 + Delta' I^2
    # auxiliary Pell
    M("Q", "Dp", "DpI2");     S("delta", "Q", 1)              # Q = Delta'^2 I^2, delta = Q - 1
    A("Tp", "T", "alpha")                                     # T' = T + alpha
    M("cT", "c", "Tp");       S("cTR", "cT", "R");      M("DfcTR", "Df", "cTR")   # cT' and b' = cT'-R
    S("V", "DfcTR", "c")                                      # V = Df(cT' - R) - c
    M("V2", "V", "V");        M("QV2", "Q", "V2");      S("Dnum", "QV2", 1)    # Dnum = Q V^2 - 1
    # main Pell radicand
    M("Dpc2", "Dp", "c2");    A("Dmain", "Dpc2", 1)           # Dmain = 1 + Delta' c^2
    # transport weight W = 1 + (q-1) L, L = 4(A'-1)I + (cT'-R) + cT'
    M("Am1I", "Am1", "I");    M("4Am1I", 4, "Am1I");    A("L1", "cTR", "cT")
    A("L", "4Am1I", "L1");    M("qm1L", "qm1", "L");    A("W", "qm1L", 1)
    # centered carrier numerator
    #   Znum = P1 mu^2 (H'(n+V) + X + a'c) + H'[mu^2((q-1)Y - q^3 W Bt) - P1 e],  P1 = q^3(q-1)
    M("P1", "q3", "qm1");     M("mu2", "mu", "mu");     M("P1mu2", "P1", "mu2")
    A("nV", "n", "V");        M("Hn", "Hp", "nV");      A("HnX", "Hn", "X");      M("apc", "ap", "c")
    A("lin", "HnX", "apc");   M("Zpart1", "P1mu2", "lin")
    M("qm1Y", "qm1", "Y");    M("WBt", "W", "Bt");      M("q3WBt", "q3", "WBt")
    S("inner", "qm1Y", "q3WBt");  M("mu2inner", "mu2", "inner")
    M("P1e", "P1", "e");      S("brk", "mu2inner", "P1e");  M("Zpart2", "Hp", "brk")
    A("Znum", "Zpart1", "Zpart2")
    # homogenized arguments s, a, b, c, d of F16
    M("Mtot", "P1mu2", "Hp")                                  # Mtot = q^3(q-1) mu^2 H'
    M("M2", "Mtot", "Mtot");  M("dM2", "delta", "M2")
    M("fa", "dM2", "Dtau");   M("fb", "dM2", "Df");     M("fc", "M2", "Dnum")
    M("P2", "P1mu2", "P1mu2"); M("dP2", "delta", "P2"); M("fd", "dP2", "Dmain")
    M("Z2", "Znum", "Znum");  M("fs", "delta", "Z2")
    # F16(s; a,b,c,d) = Ge^2 - 64 sd Go^2,  Po = U - sig1,  Pe = Po^2 + 4(sd - sig2),
    #   Ge = Pe^2 + 16(sd Po^2 - 4 sig3 U),  Go = Pe Po - 16 sig3
    A("ab", "fa", "fb");      A("sig1", "ab", "fc")
    M("aXb", "fa", "fb");     M("abXc", "ab", "fc");    A("sig2", "aXb", "abXc")
    M("sig3", "aXb", "fc")
    A("U", "fs", "fd");       S("Po", "U", "sig1");     M("sd", "fs", "fd")
    S("sdm", "sd", "sig2");   M("4sdm", 4, "sdm");      M("Po2", "Po", "Po")
    A("Pe", "Po2", "4sdm")
    M("Pe2", "Pe", "Pe");     M("sdPo2", "sd", "Po2");  M("s3U", "sig3", "U")
    M("4s3U", 4, "s3U");      S("gin", "sdPo2", "4s3U"); M("16gin", 16, "gin")
    A("Ge", "Pe2", "16gin")
    M("PePo", "Pe", "Po");    M("16s3", 16, "sig3");    S("Go", "PePo", "16s3")
    M("Ge2", "Ge", "Ge");     M("Go2", "Go", "Go");     M("sdGo2", "sd", "Go2")
    M("64sdGo2", 64, "sdGo2"); S("N", "Ge2", "64sdGo2")
    return out


def evaluate(source, env, mod=None, mul=None):
    """Evaluate rows over Z (mod=None), over Z/mod, or over any ring given by env values."""
    vals = dict(env)
    def get(x):
        if isinstance(x, int):
            return x % mod if mod is not None else x
        return vals[x]
    for name, op, x, y in source:
        u, v = get(x), get(y)
        if op == "+":
            z = u + v
        elif op == "-":
            z = u - v
        else:
            z = u * v if mul is None else mul(u, v)
        if mod is not None:
            z %= mod
        vals[name] = z
    return vals


def syntactic_degrees(source):
    deg = {v: 1 for v in WITNESSES}
    deg.update({p: 0 for p in FIXED})
    d = lambda x: 0 if isinstance(x, int) else deg[x]
    for name, op, x, y in source:
        deg[name] = d(x) + d(y) if op == "*" else max(d(x), d(y))
    return deg
