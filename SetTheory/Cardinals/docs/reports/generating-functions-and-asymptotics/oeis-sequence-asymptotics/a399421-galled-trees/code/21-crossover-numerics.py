"""High-precision finite-series checks, not interval-certified bounds."""
import json
from pathlib import Path
import mpmath as mp
ROOT = Path(__file__).resolve().parents[1]
rows = json.loads((ROOT / 'results/exact-rows.json').read_text())['rows']

def constants(cutoff, precision):
    with mp.workdps(precision):
        b = [row[0] for row in rows[:cutoff + 1]]
        def U(z):
            value = mp.mpf(0)
            for coefficient in reversed(b):
                value = value * z + coefficient
            return value
        R = mp.findroot(lambda r: 1 - 2*r - U(r*r), (mp.mpf('.4'), mp.mpf('.405')))
        A = 1 + R * mp.diff(U, R*R)
        gamma = mp.sqrt(2*R*A)
        c = 1 / (mp.sqrt(R)*A)
        d = R**(-mp.mpf(1)/4) / A
        assert abs(d*(2/c)**mp.mpf('1.5') - 2*gamma) < mp.mpf(10)**(-precision + 5)
        return dict(R=R, A=A, gamma0=gamma, c=c)

mp.mp.dps = 70
values = constants(160, 70)
R, A, gamma, c = [values[name] for name in ('R', 'A', 'gamma0', 'c')]
checks = []
for lam in [mp.mpf('.5'), mp.mpf(1), mp.mpf('1.5'), mp.mpf(2)]:
    for n in (20, 40, 80, 160):
        k = max(1, int(mp.nint(lam*mp.mpf(n)**(mp.mpf(1)/3))))
        exact = mp.mpf(rows[n][k])
        fixed = gamma/(2*mp.sqrt(mp.pi))*R**(-n)*mp.mpf(n)**(-mp.mpf('1.5'))*(c*n)**(2*k)/mp.factorial(2*k)
        correction = mp.exp(-2*gamma*mp.mpf(k)**mp.mpf('1.5')/mp.sqrt(n))
        checks.append({'n': n, 'k': k, 'nominal_lambda': mp.nstr(lam, 3),
                       'lambda': mp.nstr(k/mp.mpf(n)**(mp.mpf(1)/3), 25),
                       'exact_div_fixed': mp.nstr(exact/fixed, 35),
                       'crossover_factor': mp.nstr(correction, 35),
                       'corrected_relative_error': mp.nstr(fixed*correction/exact - 1, 35)})
results = {'numerical_status': 'Non-certified high-precision finite-series computations',
           'precision_digits': 70, 'cutoff': 160,
           'constants': {name: mp.nstr(value, 65) for name, value in values.items()},
           'checks': checks}
(ROOT / 'results/crossover-checks.json').write_text(json.dumps(results, indent=2) + '\n')

variants = [('cutoff_120_dps_70', constants(120, 70)), ('cutoff_160_dps_50', constants(160, 50))]
stability = {}
for name, variant in variants:
    diff = {key: abs(variant[key] - values[key]) for key in values}
    assert max(diff.values()) < mp.mpf('1e-40')
    stability[name] = {key: mp.nstr(value, 15) for key, value in diff.items()}
(ROOT / 'results/stability.json').write_text(json.dumps({'absolute_differences': stability, 'certified': False}, indent=2) + '\n')

selected = [item for item in checks if item['nominal_lambda'] == '1.0']
selected += [item for item in checks if item['n'] == 160 and item['nominal_lambda'] != '1.0']
lines = []
for item in selected:
    lines.append(f"{item['n']} & {item['k']} & {float(item['lambda']):.4f} & {float(item['exact_div_fixed']):.7f} & {float(item['crossover_factor']):.7f} & {float(item['corrected_relative_error']):+.5f} \\\\")
header = r'\begin{tabular}{rrrrrr}' + '\n' + r'\toprule' + '\n' + r'$n$&$k$&$k/n^{1/3}$&$E/L_0$&$q_n$&Corrected error\\' + '\n' + r'\midrule' + '\n'
footer = r'\bottomrule' + '\n' + r'\end{tabular}' + '\n'
(ROOT / 'results/checks-table.tex').write_text(header + '\n'.join(lines) + '\n' + footer)
print(json.dumps(results, indent=2))
print('Stability checks:', json.dumps(stability, indent=2))
