import sys; sys.path.insert(0, '.')
from tmlib import *
T, s = load(sys.argv[1]); N0 = int(sys.argv[2]); N1 = int(sys.argv[3])
R = Run(T, s)
while R.t < N0: assert R.step()
def rle(R, lo=-14, hi=None):
    o = R.ones(); hi = max(o + [R.head]) + 1
    out = []; i = lo
    while i <= hi:
        b = R.tape.get(i, 0); j = i
        while j + 1 <= hi and R.tape.get(j + 1, 0) == b and j + 1 != R.head and i != R.head: j += 1
        tok = ('%d' % b) if j == i else ('%d^%d' % (b, j - i + 1))
        if i == R.head: tok = '[' + tok + ']'
        out.append(tok); i = j + 1
    return ' '.join(out[:34])
prev = None
while R.t < N1:
    st = R.state
    cat = 'node' if st.startswith('node_') else st
    if cat != prev or not st.startswith(('node_','4.dispatch','2b.reg','2c','6.cont','1b','new.seek','2e')):
        print('%7d %-22s @%-4d %s' % (R.t, st, R.head, rle(R)))
    prev = cat
    if not R.step(): print('HALT/undefined', R.state); break
