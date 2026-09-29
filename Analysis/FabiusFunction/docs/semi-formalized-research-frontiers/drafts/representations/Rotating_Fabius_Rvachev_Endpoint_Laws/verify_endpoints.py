#!/usr/bin/env python3
"""Reproduce deterministic checks accompanying the rotating-endpoint article.

Requires Python 3.10+ and mpmath. No network, random sampling, or proof assistant.
Analytic truncation bounds are reported separately from floating-point error.
The latter is checked by a second precision, not certified by interval arithmetic.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
from typing import Callable
import mpmath as mp


def kernel(z: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Return h(z), J(exp(z)), and V(exp(z)), including z=-infinity.

    h=-log Laplace of U[0, exp(z)]; J and V are its tilted mean and
    variance. An exponential cutoff discards less than 10^(-dps-10)
    in the large-u branch. Small-u cancellations get extra precision.
    """
    if z == mp.ninf:
        return mp.mpf(0), mp.mpf(0), mp.mpf(0)
    cutoff = (mp.mp.dps + 30) * mp.log(10)
    if z > mp.log(cutoff):
        return z, mp.mpf(1), mp.mpf(1)
    u = mp.exp(z)
    # V has cancellation of order u^2; preserve requested precision.
    extra = max(20, int(mp.ceil(max(mp.mpf(0), -2*z/mp.log(10)))) + 15)
    with mp.extradps(extra):
        em = mp.expm1(u)
        h = mp.log(u / (-mp.expm1(-u)))
        j = 1-u/em
        v = 1-u*u*mp.exp(u)/(em*em)
    return +h, +j, +v


def baseline(t: mp.mpf, lam: mp.mpf) -> mp.mpf:
    n = max(0, int(mp.floor(t/lam)))
    return n*t-lam*n*(n+1)/2


def evaluate(t: mp.mpf, lam: mp.mpf,
             amplitude: Callable[[int], mp.mpf], digits: int = 40) -> dict:
    """Evaluate an amplitude sequence 0<=a_n<=2, with b_n=q^n a_n."""
    if lam <= 0 or t < 0 or digits < 8:
        raise ValueError("Require lambda>0, t>=0, and digits>=8.")
    q = mp.exp(-lam)
    # Tail H <= e^t q^(M+1)/(1-q). J obeys the same bound.
    m = max(1, int(mp.ceil((t+digits*mp.log(10)-mp.log(1-q))/lam)))
    hs, js, vs = [], [], []
    profile = mp.mpf(0)
    for n in range(1, m+1):
        a = amplitude(n)
        if a < 0 or a > 2+mp.eps*8:
            raise ValueError("Amplitude must be in [0,2].")
        f = mp.log(a) if a else mp.ninf
        h, j, v = kernel(t-lam*n+f)
        hs.append(h); js.append(j); vs.append(v)
        if lam*n <= t:
            depth = max(mp.mpf(0), -f)
            profile = max(profile, min(depth, t-lam*n))
    h, j, v = map(mp.fsum, (hs, js, vs))
    b = baseline(t, lam)
    return {"t": t, "terms": m, "H": h, "H_prime": j,
            "tilted_variance": v, "B": b, "R": profile,
            "H_minus_B_plus_R": h-b+profile,
            "scaled_residual": (h-b+profile)/mp.log(2+t)**2,
            "H_prime_over_t_lambda": j/(t/lam) if t else mp.nan,
            "variance_over_t_lambda": v/(t/lam) if t else mp.nan,
            "H_and_J_tail_bound": mp.exp(t)*q**(m+1)/(1-q),
            "variance_tail_bound": 4*mp.exp(2*t)*q**(2*(m+1))/(1-q*q)}


def serial(row: dict) -> dict:
    return {k: mp.nstr(v, 24) if isinstance(v, mp.mpf) else v
            for k,v in row.items()}


def run(output: Path, dps: int) -> None:
    if dps < 90:
        raise ValueError("Use at least 90 digits for the engineered phase.")
    mp.mp.dps = dps
    output.mkdir(parents=True, exist_ok=True)
    lam = mp.log(2)
    alpha = (mp.sqrt(5)-1)/2
    beta_spike = mp.mpf('0.5')-20*alpha+mp.exp(-120)
    cases = [("golden_beta_0", mp.mpf(0)),
             ("golden_beta_half", mp.mpf('0.5')),
             ("golden_engineered_phase", beta_spike)]
    rows = []
    for name, beta in cases:
        for t0 in (20,40,80,120,160):
            amp = lambda n, beta=beta: 2*abs(mp.cospi(n*alpha+beta))
            r = evaluate(mp.mpf(t0), lam, amp)
            r["case"] = name
            rows.append(serial(r))

    rational_rows = []
    for denominator in (7,13,23,41):
        r = denominator
        # beta=1/2, alpha=1/r. Multiples are exactly zero, not rounded sine.
        amp = lambda n, r=r: (mp.mpf(0) if n % r == 0
                              else 2*abs(mp.sinpi(mp.mpf(n % r)/r)))
        t = mp.mpf(r*r)
        row = evaluate(t, lam, amp)
        defect = row['B']-row['H']
        main = t*t/(2*lam*r)
        row.update({"denominator": r, "defect": defect,
                    "predicted_defect": main, "defect_ratio": defect/main,
                    "irrational_transfer_bound": mp.pi*mp.exp(-lam)/
                        (1-mp.exp(-lam))**2*mp.exp(-t)})
        rational_rows.append(serial(row))

    # Numerical consistency tests, not logical proofs.
    checks = []
    for t in map(mp.mpf, ('0', '0.1', '1', '5', '20', '39.2')):
        n = int(mp.floor(t/lam))
        b_sum = mp.fsum([max(mp.mpf(0),t-lam*k) for k in range(1,n+2)])
        frac = t/lam-n
        b_closed = t*t/(2*lam)-t/2+lam*frac*(1-frac)/2
        assert abs(b_sum-b_closed) < mp.mpf('1e-75')
    checks.append("baseline sum agrees with the exact fractional-part formula")
    for z in map(mp.mpf, ('-3', '-1', '0', '1', '2')):
        h,j,v = kernel(z)
        hp = mp.diff(lambda w: kernel(w)[0], z)
        jprime = mp.diff(lambda w: kernel(w)[1], z)
        assert abs(hp-j) < mp.mpf('1e-65')
        assert abs(j-jprime-v) < mp.mpf('1e-65')
        assert 0 <= j <= 1 and 0 <= v <= 1
    checks.append("h'=J and J-J'=V checked by numerical differentiation")

    amp = lambda n: 2*abs(mp.cospi(n*alpha+beta_spike))
    p1 = evaluate(mp.mpf(80),lam,amp)['R']
    p2 = evaluate(mp.mpf('80.25'),lam,amp)['R']
    assert 0 <= p2-p1 <= mp.mpf('0.25')+mp.mpf('1e-70')
    checks.append("profile monotonicity and Lipschitz bound checked on one increment")

    with mp.workdps(dps+35):
        alpha_hi = (mp.sqrt(5)-1)/2
        beta_hi = mp.mpf('0.5')-20*alpha_hi+mp.exp(-120)
        rh = evaluate(mp.mpf(120),mp.log(2),
                      lambda n: 2*abs(mp.cospi(n*alpha_hi+beta_hi)))
    # Stored rows have 24 significant digits. Compare the full-precision run too.
    rl = evaluate(mp.mpf(120),lam,amp)
    precision_difference = abs(rl['H']-rh['H'])
    assert precision_difference < mp.mpf('1e-30')
    checks.append("engineered phase at t=120 agrees after adding 35 precision digits")

    # Saddle equation check at prescribed x: bisection, no assumption of monotonic H'.
    x = mp.exp(-20)
    target = -mp.lambertw(-lam*x,-1).real
    lo, hi = target-1, target+1
    amp0 = lambda n: 2*abs(mp.cospi(n*alpha))
    for _ in range(100):
        mid = (lo+hi)/2
        val = evaluate(mid,lam,amp0,digits=30)
        if val['H_prime']*mp.exp(-mid) > x:
            lo = mid
        else:
            hi = mid
    tx = (lo+hi)/2
    sx = evaluate(tx,lam,amp0,digits=30)
    saddle = {"L": "20", "Lambert_T": mp.nstr(target,24),
              "saddle_t": mp.nstr(tx,24),
              "difference": mp.nstr(tx-target,24),
              "relative_equation_residual": mp.nstr(
                  abs(sx['H_prime']*mp.exp(-tx)/x-1),24),
              "log_C_saddle_approximation": mp.nstr(
                  mp.exp(tx)*x-sx['H']-mp.log(2*mp.pi*sx['tilted_variance'])/2,24)}
    checks.append("unique saddle equation solved by deterministic bisection")

    for name, data in (("bounded_type_checks.csv",rows),
                       ("rational_resonance_checks.csv",rational_rows)):
        with (output/name).open('w',newline='') as f:
            writer = csv.DictWriter(f,fieldnames=list(data[0]))
            writer.writeheader(); writer.writerows(data)
    write_latex_tables(output, rows, rational_rows)

    report = {"precision_digits": dps,
              "normalization": "q=1/2; b_n=2*q^n*abs(cos(pi*(n*alpha+beta)))",
              "checks_passed": checks,
              "precision_comparison_absolute_H_difference":
                  mp.nstr(precision_difference,24),
              "saddle_check": saddle,
              "limitations": ["No formal proof verification.",
                  "No interval-arithmetic rounding certificate.",
                  "Tail bounds are analytic bounds; floating-point error is separate.",
                  "Finite examples do not establish infinite-subsequence results.",
                  "No independent numerical computation of the exact cap CDF."]}
    (output/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


def write_latex_tables(output: Path, rows: list[dict], rational_rows: list[dict]) -> None:
    """Export the small, six-decimal display tables included in article.tex."""
    lines = [r'\begin{tabular}{@{}llrrr@{}}', r'\toprule',
             r'Phase & $t$ & $R_\beta(t)$ & $H-B+R$ & $H^\prime/(t/\lambda)$ \\',
             r'\midrule']
    for row in rows:
        if row['case'] == 'golden_beta_half' or row['t'] not in ('40.0','80.0','120.0','160.0'):
            continue
        name = r'$\beta=0$' if row['case'] == 'golden_beta_0' else 'engineered phase'
        lines.append(f"{name} & {float(row['t']):.0f} & {float(row['R']):.6f} & "
                     f"{float(row['H_minus_B_plus_R']):.6f} & "
                     f"{float(row['H_prime_over_t_lambda']):.6f} " + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (output/'bounded_type_table.tex').write_text('\n'.join(lines)+'\n')
    lines = [r'\begin{tabular}{@{}rrrrr@{}}', r'\toprule',
             r'$r$ & $t=r^2$ & $\Delta_{1/r}(t)$ & $t^2/(2\lambda r)$ & ratio \\',
             r'\midrule']
    for row in rational_rows:
        lines.append(f"{int(row['denominator'])} & {float(row['t']):.0f} & "
                     f"{float(row['defect']):.6f} & {float(row['predicted_defect']):.6f} & "
                     f"{float(row['defect_ratio']):.6f} " + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (output/'rational_table.tex').write_text('\n'.join(lines)+'\n')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data'))
    parser.add_argument('--dps',type=int,default=110)
    args = parser.parse_args()
    run(args.output,args.dps)

if __name__ == '__main__':
    main()
