"""Generate the quadratic characters and rational enclosures for group enumeration.

Run python quadratic_input.py /path/to/check_exterior.py > quadratic.json .
"""
from importlib.util import module_from_spec, spec_from_file_location
from fractions import Fraction
import sys
import json

def load(path):
    spec = spec_from_file_location("quadratic_intervals",path)
    lib = module_from_spec(spec)
    spec.loader.exec_module(lib)
    return lib

def key(d, lib):
    rad = d//4 if d % 4 == 0 else d
    dyadic = d
    coords = []
    for p in lib.distinct_factors(abs(rad)):
        if p > 2:
            dyadic //= p if p % 4 == 1 else -p
            coords.append((p,1,2))
    if dyadic in (-4,-8):
        coords.append((-2,1,2))
    if dyadic in (-8,8):
        coords.append((2,1,2))
    return sorted(coords)

def bounds(v):
    unit = 10**13
    # All quantities are positive. One extra unit on each side safely covers
    # conversion of the mpmath interval endpoints to decimal rationals.
    return str(Fraction(int((v*unit).a)-1,unit)), str(Fraction(int((v*unit).b)+2,unit))

def main():
    lib = load(sys.argv[1])
    lib.P, lib.Q = 24, 1202
    w = lib.weights()
    iv = lib.iv
    zeta = 2 + iv.euler - iv.log(4*iv.pi)
    out = []
    for d in range(-551,1202):
        if d in (0,1):
            continue
        chi = lib.character(d)
        if chi is None:
            continue
        val = lib.enclosure(d,chi,w)
        if val+zeta < 2:
            lo,hi = bounds(val)
            out.append({"q":abs(d),"d":d,"character":key(d,lib),"B_lower":lo,"B_upper":hi})
        elif not val+zeta > 2:
            raise ArithmeticError(f"Undecided at {d}")
    low, high = bounds(zeta)
    print(json.dumps({"B1_lower":low,"B1_upper":high,"characters":out},indent=2))

if __name__ == "__main__":
    main()
