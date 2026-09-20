#!/usr/bin/env python3
"""Reproduce exact data and asymptotic diagnostics for OEIS A277364.

No network access is used. Exact counts use Python integers; asymptotic
quantities use mpmath. Run from the archive root:
    python code/analyze.py --max-n 2001 --plots
An optional OEIS b-file can be checked with --oeis-file PATH.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
import sys
from typing import Iterator

import mpmath as mp

PREFIX = [
    1, 0, 1, 1, 8, 16, 122, 365, 2795, 11051, 86472, 422005,
    3403127, 19628064, 164029595, 1084948961, 9433737120,
    69998462014, 635182667816, 5199414528808, 49344452550230,
    439841775811967, 4371727233798927, 42000637216351225,
    437489737355466560, 4493269587087402967,
]


def stirling_rows(max_n: int) -> Iterator[tuple[int, list[int]]]:
    """Yield rows [S(n,0),...,S(n,n)] in O(max_n^2) integer operations."""
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    row = [1]
    yield 0, row
    for n in range(1, max_n + 1):
        row = [0] + [k * (row[k] if k < len(row) else 0) + row[k-1]
                     for k in range(1, n + 1)]
        yield n, row


def constants() -> dict[str, mp.mpf]:
    tau = 2 + mp.lambertw(-2 * mp.exp(-2), 0)
    g = mp.expm1(tau)
    v = 2 * (tau - 1)
    kappa3 = 2 * (tau**2 - 3*tau + 3)
    kappa4 = 2 * (tau**3 - 8*tau**2 + 19*tau - 13)
    return dict(tau=tau, g=g, v=v, kappa3=kappa3, kappa4=kappa4,
                C=mp.sqrt(2*g/mp.e)/tau, rho=2*g)


def local_correction(d: mp.mpf, c: dict[str, mp.mpf]) -> mp.mpf:
    v, k3, k4 = c['v'], c['kappa3'], c['kappa4']
    return k4/(8*v**2) - 5*k3**2/(24*v**3) - k3*d/(2*v**2) - d**2/(2*v)


def tail_correction(delta: mp.mpf, c: dict[str, mp.mpf]) -> mp.mpf:
    return (2*c['g'] - delta**2 - 2*delta - mp.mpf(1)/12
            + 2*local_correction(-2*delta, c))


def diagnostics(n: int, row: list[int], c: dict[str, mp.mpf]) -> dict:
    """Compute relative errors without subtracting nearly equal Bell counts."""
    if n < 2:
        raise ValueError("asymptotic diagnostics start at n=2")
    K = n//2 + 1
    a, B, D, endpoint = sum(row[:K]), sum(row), sum(row[K:]), row[K]
    nn = mp.mpf(n)
    r = mp.lambertw(nn)
    delta = mp.mpf(K) - nn/2
    logF = nn*(r - 1 + 1/r) - 1 - mp.log1p(r)/2
    P = r**2*(2*r**2 + 7*r + 10)/(24*(1+r)**3)
    F = mp.exp(logF)
    F1 = F*(1-P/nn)
    logD0 = (nn*(mp.log(c['C']) + mp.log(nn)/2)
             - (delta+mp.mpf('0.5'))*mp.log(nn)
             + delta*mp.log(2*c['g']) - mp.log(mp.pi*(c['tau']-1))/2)
    D0 = mp.exp(logD0)
    J = tail_correction(delta, c)
    D1 = D0*(1+J/nn)
    return dict(n=n, K=K, delta=delta,
                log10_a=mp.log10(a), log10_B=mp.log10(B),
                log10_D=mp.log10(D), deficit=mp.mpf(D)/B,
                log10_deficit=mp.log10(D)-mp.log10(B),
                F_over_a_minus_1=F/a-1,
                F1_over_a_minus_1=F1/a-1,
                F_over_B_minus_1=F/B-1,
                F1_over_B_minus_1=F1/B-1,
                D0_over_D_minus_1=D0/D-1,
                D1_over_D_minus_1=D1/D-1,
                n_tail_endpoint_excess=nn*(mp.mpf(D)/endpoint-1),
                tail_correction=J,
                scaled_log_deficit=(mp.log(D)-mp.log(B))/(nn*mp.log(nn)))


def read_reference(path: Path) -> dict[int, int]:
    result = {}
    for line in path.read_text(encoding='utf-8').splitlines():
        line = line.split('#', 1)[0].strip()
        if line:
            fields = line.split()
            if len(fields) != 2:
                raise ValueError(f"invalid b-file line: {line[:80]}")
            result[int(fields[0])] = int(fields[1])
    return result


def make_plots(records: list[dict], directory: Path) -> None:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    directory.mkdir(parents=True, exist_ok=True)
    fig, ax = plt.subplots(figsize=(7, 4.1))
    for parity, label in [(0, 'Even n'), (1, 'Odd n')]:
        rs = [r for r in records if 10 <= r['n'] <= 400 and r['n'] % 2 == parity]
        ax.plot([r['n'] for r in rs], [float(r['log10_deficit']) for r in rs],
                label=label)
    ax.set_xlabel('n')
    ax.set_ylabel(r'$\log_{10}((B_n-a(n))/B_n)$')
    ax.set_title('The relative contribution of the omitted partitions')
    ax.grid(True, alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(directory/'relative_deficit.pdf')
    fig.savefig(directory/'relative_deficit.png', dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7, 4.1))
    rs = [r for r in records if 50 <= r['n'] <= 2000 and r['n'] % 2 == 0]
    for key, label in [('F_over_a_minus_1', r'$F(n)$'),
                       ('F1_over_a_minus_1', r'$F(n)(1-P(r)/n)$')]:
        ax.loglog([r['n'] for r in rs], [abs(float(r[key])) for r in rs], label=label)
    ax.set_xlabel('n (even values)')
    ax.set_ylabel('Absolute relative error')
    ax.set_title('Leading and first-corrected approximations to a(n)')
    ax.grid(True, which='both', alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(directory/'bell_accuracy.pdf')
    fig.savefig(directory/'bell_accuracy.png', dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7, 4.1))
    for parity, ptext in [(0, 'even'), (1, 'odd')]:
        rs = [r for r in records if 50 <= r['n'] <= 2001 and r['n'] % 2 == parity]
        for key, name in [('D0_over_D_minus_1', 'leading'),
                          ('D1_over_D_minus_1', 'corrected')]:
            ax.loglog([r['n'] for r in rs], [abs(float(r[key])) for r in rs],
                      label=f'{name}, {ptext} n')
    ax.set_xlabel('n')
    ax.set_ylabel('Absolute relative error')
    ax.set_title('Parity-sensitive approximations to the omitted tail')
    ax.grid(True, which='both', alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(directory/'tail_accuracy.pdf')
    fig.savefig(directory/'tail_accuracy.png', dpi=180)
    plt.close(fig)


def run(args: argparse.Namespace) -> None:
    if args.max_n < 25 or args.dps < 40 or args.exact_through < 0:
        raise ValueError('require max-n >= 25, dps >= 40, exact-through >= 0')
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    mp.mp.dps = args.dps
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    c = constants()
    ref = read_reference(args.oeis_file) if args.oeis_file else {}
    bells: list[int] = []
    records = []
    checked_ref = 0
    with (out/'a277364_exact.txt').open('w') as exact_file:
        exact_file.write('# Independently computed A277364: n a(n)\n')
        for n, row in stirling_rows(args.max_n):
            K = n//2+1
            a, B, D = sum(row[:K]), sum(row), sum(row[K:])
            assert a+D == B
            if n < len(PREFIX):
                assert a == PREFIX[n], (n, a, PREFIX[n])
            if n in ref:
                assert a == ref[n], (n, a, ref[n])
                checked_ref += 1
            if n <= 400:
                if n > 0:
                    check = sum(math.comb(n-1, j)*bells[j] for j in range(n))
                    assert B == check, (n, B, check)
                bells.append(B)
            if n <= min(args.max_n, args.exact_through):
                exact_file.write(f'{n} {a}\n')
            if n >= 2:
                records.append(diagnostics(n, row, c))
    log_mgf = lambda s: mp.log(mp.expm1(c['tau']*mp.exp(s)))-mp.log(c['g'])
    for degree, expected in [(1, mp.mpf(2)), (2, c['v']),
                             (3, c['kappa3']), (4, c['kappa4'])]:
        assert mp.almosteq(mp.diff(log_mgf, 0, degree), expected)
    summary = {
        'max_n_exact_counts': args.max_n,
        'precision_decimal_digits': args.dps,
        'oeis_prefix_checked_n_0_through': 25,
        'independent_Bell_recurrence_checked_n_0_through': min(args.max_n, 400),
        'optional_reference_entries_checked': checked_ref,
        'cumulant_derivatives_checked': [1, 2, 3, 4],
        'constants': {k: mp.nstr(v, 60) for k, v in c.items()},
        'tail_J_even': mp.nstr(tail_correction(mp.mpf(1), c), 60),
        'tail_J_odd': mp.nstr(tail_correction(mp.mpf('0.5'), c), 60),
        'tail_A_even': mp.nstr(2*c['g']/mp.sqrt(mp.pi*(c['tau']-1)), 60),
        'tail_A_odd': mp.nstr(mp.sqrt(2*c['g'])/mp.sqrt(mp.pi*(c['tau']-1)), 60),
        'status': 'all executed exact and numerical consistency checks passed',
        'interpretation': 'Finite checks support, but do not replace, the proofs.',
    }
    (out/'verification.json').write_text(json.dumps(summary, indent=2)+'\n')
    with (out/'diagnostics.csv').open('w', newline='') as file:
        writer = csv.DictWriter(file, fieldnames=list(records[0]))
        writer.writeheader()
        for r in records:
            writer.writerow({k: (v if isinstance(v, int) else mp.nstr(v, 35))
                             for k, v in r.items()})
    selected = {10, 11, 20, 21, 50, 51, 100, 101, 200, 201, 400, 401, 1000, 1001, 2000, 2001}
    with (out/'selected_diagnostics.txt').open('w') as file:
        for r in records:
            if r['n'] in selected:
                file.write('n='+str(r['n'])+'\n')
                for k in ['deficit', 'F_over_a_minus_1', 'F1_over_a_minus_1',
                          'D0_over_D_minus_1', 'D1_over_D_minus_1',
                          'n_tail_endpoint_excess', 'scaled_log_deficit']:
                    file.write(f'  {k}: {mp.nstr(r[k], 15)}\n')
    if args.plots:
        make_plots(records, args.figures)
    print(json.dumps(summary, indent=2))


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=2001)
    parser.add_argument('--exact-through', type=int, default=1000)
    parser.add_argument('--dps', type=int, default=80)
    parser.add_argument('--output', type=Path, default=root/'data')
    parser.add_argument('--figures', type=Path, default=root/'figures')
    parser.add_argument('--oeis-file', type=Path)
    parser.add_argument('--plots', action='store_true')
    args = parser.parse_args()
    try:
        run(args)
    except (ValueError, OSError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
