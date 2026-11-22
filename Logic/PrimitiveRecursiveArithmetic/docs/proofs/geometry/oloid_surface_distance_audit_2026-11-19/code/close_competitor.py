"""Verify the exact runner-up via B for P6 to P9, including endpoint status."""
import json
from pathlib import Path
from fractions import Fraction as Q
import geometry as g
import verify as cert
from verify_roots import derivatives, minus, dot, square, fixed_point

def prove(build=False):
    p, q = (cert.center(g.point_box(name)) for name in ('P6','P9'))
    end = cert.witness(p,q,'B',(Q(1),))
    hi = cert.upper(end)
    radius = Q(1,1024)
    cell = (1-radius,Q(1))
    path = Path(__file__).resolve().parents[1] / 'data' / 'close_tree.json'
    tree = None if build else json.loads(path.read_text())
    tree = cert.inspect_word(p,q,'B',hi+1,(Q(1),),tree,(cell,))
    if build:
        path.write_text(json.dumps(tree)+'\n')
    a,velocity,_ = derivatives('B',cell)
    slope = g.iv(0)
    for name in ('P6','P9'):
        r = minus(a,fixed_point(name))
        length = (square(r[0])+square(r[1])).sqrt()
        slope += dot(r,velocity)/length
    cert.require(slope.hi < 0, 'slope sign not resolved')
    print('P6-P9 B competitor uniquely minimized at f=1; slope upper bound',
          Q(slope.hi,g.UNIT))
if __name__=='__main__':
    import sys
    prove('--build' in sys.argv[1:])
