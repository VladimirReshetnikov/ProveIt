#!/usr/bin/env python3
"""Generate deterministic TeX table macros from the computation JSON."""
from pathlib import Path
import mpmath as mp


def tex_number(value, digits=12):
    value = mp.nstr(mp.mpf(value), digits)
    if 'e' in value:
        mantissa, exponent = value.split('e')
        return r'\(' + mantissa + r'\times 10^{' + str(int(exponent)) + r'}\)'
    return r'\(' + value + r'\)'


def _table(name, columns, heading, rows):
    return ('\\newcommand{\\' + name + '}{%\n'
            '\\begin{tabular}{' + columns + '}\n\\hline\n'
            + heading + ' \\\\\n\\hline\n'
            + ''.join(' & '.join(row) + ' \\\\\n' for row in rows)
            + '\\hline\n\\end{tabular}%\n}\n')


def write_tables(result, destination):
    mp.mp.dps = 85
    out = '% Generated deterministically by build.py; ordinary numerical diagnostics.\n'
    out += _table('ReportCoefficientTable','rll',r'$r$ & $c_r$ & $\ell_r$',
                  [[str(r),tex_number(result['coefficients'][r],17),
                    '--' if r == 0 else tex_number(result['logarithmic_coefficients'][r],17)]
                   for r in range(5)])
    out += _table('ReportForwardTable','rll',
                  r'$n$ & $R_n/Q(1)$ & $n^5(R_n/Q-\sum_{r=0}^4c_r/n^r)$',
                  [[str(row['n']),tex_number(row['R_over_Q'],13),tex_number(row['scaled_remainders'][4],11)]
                   for row in result['forward']])
    out += _table('ReportInverseTable','rlll',
                  r'$n$ & $t-n$ & $\widetilde x_2-n$ & $x_4-n$',
                  [[str(row['n']),tex_number(row['t_minus_n'],9),
                    tex_number(row['profile_errors'][2],9),tex_number(row['H4_root_minus_n'],9)]
                   for row in result['inverse']])
    out += _table('ReportCutoffTable','rl',r'$r$ & Cutoff majorant ($J=200$, $\theta=0.09$)',
                  [[str(row['r']),tex_number(row['total_majorant_diagnostic'],9)]
                   for row in result['cutoff']])
    out += _table('ReportTVTable','rl',r'$n$ & $n\,\mathrm{TV}(P_n,\nu_1)$',
                  [[str(row['n']),tex_number(row['n_times_TV'],12)] for row in result['TV']])
    Path(destination).write_text(out,encoding='utf-8')
