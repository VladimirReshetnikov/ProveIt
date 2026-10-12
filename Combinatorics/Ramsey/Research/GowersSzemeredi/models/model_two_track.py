"""Two-track split invariant: (ac, Dc) for count and threshold, (ae, De) for the width exponent.
Dependencies read off Proofs16SplitStepBounds: Qr, S, Pb, divisor q, width scale Z from the count;
Eb and Er from the exponent. Combined by max (L.16w)."""
import sys
sys.path.insert(0, r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\models')
import model_split_exact as M
exec(open('model_jsens.py', encoding='utf-8').read().split("print('baseline")[0])
src = open('model_ksens.py', encoding='utf-8').read()
exec(src[src.index('def runK'):src.index("print('K baseline")])
def step(k, ac, Dc, ae, De):
    p, t = M.P(k), M.T(k)
    # count side (unchanged recursion, count inputs only)
    sQr = ac * 2 ** k; sS = sQr + 1; sPb = ac * (sS + 1)
    acn = 1 + 2 * sS + 2 * sPb
    stepYc = ac * (p + 1) + Dc * (p + k + 6)
    SW = stepYc * 2 ** k + p + 8
    PbW = ac * (p + SW + 1) + Dc * (p + 5)
    cW = p + 1 + 2 * SW + 2 * PbW
    thr = Dc * (p + 2) + p + 2
    Dcn = max(cW, thr)
    # exponent side
    EbWc = ac * (p + 1) + Dc * (p + 6)          # divisor q and Z: count at rho/8
    EbWe = ae * (p + 1) + De * (p + 6)          # Eb: exponent at rho/8
    stepYe = ae * (p + 1) + De * (p + k + 6)
    ErW = (stepYe + 4) * 2 ** k                 # Er: exponent at the vertices
    BqW = 4 + (EbWc + 1) * 2 ** (k + 2)
    LW = BqW + (ErW + EbWe)
    ZW = t + ac + EbWc + 7
    eW = ZW + LW + PbW + 6
    aen = 1 + (ac * 2 ** (k + 2) + ae * 2 ** k + ae) + sPb
    return acn, Dcn, aen, eW
def table(seedc, seede, kmax=15):
    ac, Dc = seedc; ae, De = seede
    tab = {2: max(M.log2ceil(ac + Dc + 3), M.log2ceil(ae + De + 3))}
    for k in range(2, kmax - 1):
        ac, Dc, ae, De = step(k, ac, Dc, ae, De)
        l = k + 1
        tab[l] = max(M.log2ceil(ac + Dc + l + 1), M.log2ceil(ae + De + l + 1))
    return [17, 17] + [tab[l] for l in range(2, kmax)]
t2 = table((11, 2 ** 41), (29, 2 ** 46))
print('two-track (11,2^41)/(29,2^46):', t2[2:])
print('  18.1', run(tab=t2)[0], '18.2', runK(tab=t2))
t3 = table((32, 2 ** 48), (32, 2 ** 48))
print('one-track check (32,2^48), max:', t3[2:9])
