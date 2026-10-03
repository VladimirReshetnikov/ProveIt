"""Exact side constants for the diagonal and tangent lower bounds."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from fractions import Fraction as F
from pathlib import Path
import json
alpha=F(707,275)
assert alpha>2 and 2**128>4*20*128
rate=F(7,4)/alpha
assert 26000*128**3*rate**128<F(3,20)
assert rate*F(129,128)**3<1
assert 128**2-F(25,2)*128-F(385,8)>0
assert F(5,3**4)<F(4,3*7)
assert 2*F(22,7)*3*F(13,12)<25
out=dict(all_checks_passed=True,diagonal_cutoff_d=128,diagonal_ratio=str(rate),
         cosine_absorption=True,coefficient_log_concavity_base_case=True,
         entropy_constant_less_than_5=True)
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('coefficient_lower_bounds_certificate.json', json.dumps(out,indent=2)+'\n')
print('Diagonal, log-concavity, entropy and cosine constants pass.')
