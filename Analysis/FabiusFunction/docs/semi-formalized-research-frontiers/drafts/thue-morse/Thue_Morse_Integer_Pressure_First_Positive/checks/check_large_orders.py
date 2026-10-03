"""Numerical regression for the proved large-order expansion; not interval arithmetic."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# data/rerun/ in the package, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parents[1] / 'data' / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=80
root=Path(__file__).resolve().parent.parent
S0=mp.fsum(mp.tan(mp.pi/mp.mpf(2)**(j+1)) for j in range(1,280))
U0=mp.fsum(mp.tan(mp.pi/mp.mpf(2)**(j+1))**2 for j in range(1,280))
rows=[]
for row in json.loads((root/'data'/'second_response_checks.json').read_text())['rows']:
 m=row['m']; numerator,denominator=row['C'].split('/');C=mp.mpf(numerator)/mp.mpf(denominator)
 main=(2/mp.pi)**(2*m)*(4*m*m*S0*S0+m*(mp.mpf(4)/3-2*U0)-8*mp.mpf(m)/((m+1)*mp.pi**2))
 error=abs(C-main)
 # A coarse explicit consequence of the proved orbit and atomic-value tails.
 bound=mp.mpf(2200)*m*m*(2/(3*mp.pi))**(2*m)
 assert error<bound
 rows.append({'m':m,'C':str(C),'main':str(main),'absolute_error':str(error),'analytic_tail_bound':str(bound)})
result={'S0':str(S0),'U0':str(U0),'leading_constant_4S0_squared':str(4*S0*S0),'rows':rows,'all_checks_passed':True,'numerical_scope':'80-digit floating arithmetic; analytic bounds are proved in the manuscript, not certified by these numerical comparisons'}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('large_order_checks.json', json.dumps(result,indent=2)+'\n')
print('Large-order formula checked for m=2,...,10; S0 =',mp.nstr(S0,22),' U0 =',mp.nstr(U0,22))
