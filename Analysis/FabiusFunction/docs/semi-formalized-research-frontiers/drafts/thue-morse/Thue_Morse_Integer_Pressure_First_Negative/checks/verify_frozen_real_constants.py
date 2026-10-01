"""Rational side conditions for the principal-branch asymptotic."""
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
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_intervals import I,iv,PI,S,sinp,cosp

def require(c,msg):
 if not c:raise ArithmeticError(msg)

def H(a,x):
 z=iv(1)
 for j in range(1,33):z=z*(cosp(x/F(2**j))+a*sinp(x/F(2**j)))
 # The omitted factors are >=1 because their angles are <a. They are <=exp(a sum angles).
 tail=iv(a*x/F(2**32))*PI
 upper=z/(1-tail)
 return I(z.lo,upper.hi)
la=H(F(7,20),F(1,2));ha=H(F(19,50),F(3,4))
checks={
 'L_lower':F(la.lo,S)>F(28,25),
 'H_three_quarters_upper':F(ha.hi,S)<F(9,10),
 'secondary_weight':F(13,20)**2/2<F(23,50)**2,
 'Q_half_below_095':F(23,50)*F(9,10)/(F(7,20)*F(28,25)**2)<F(19,20),
 'sin_pi_eighth':F(sinp(F(1,8)).hi,S)<F(383,1000),
 'cos_pi_eighth':F(cosp(F(1,8)).lo,S)>F(923,1000),
 'Q_quarter_below_quarter':F(3,50)*F(7,5)/F(7,20)<F(1,4),
 'quarter_weight':F(383,1000)-F(7,20)*F(923,1000)<F(3,50),
 'positive_Q_small_x':F(sinp(F(1,16)).hi,S)<F(7,20)*F(cosp(F(1,16)).lo,S),
 'g_lower':F(7,20)*F(28,25)>F(39,100),
 'secondary_error_gap':F(23,50)*F(7,5)*F(49,100)<F(343,1000)<F(39,100),
 'rank_one_error_gap':F(19,50)*F(11907,20000)<F(343,1000),
}
require(all(checks.values()),'frozen real-side condition')
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('frozen_real_constants.json', json.dumps(dict(all_checks_passed=True,checks=checks,L_lower=str(F(la.lo,S)),H_three_quarters_upper=str(F(ha.hi,S)),mathematical_asymptotic_proved_in_article=True),indent=2)+'\n')
print('All real principal-branch constants pass; the analytic argument is given in the article.')
