#!/usr/bin/env python3
"""Independent static Report 64 manuscript checks; no scientific source executes.

Read-only inputs; outputs are restricted to this sibling audit directory. The
script checks literal displayed formula/rule tokens, independently transcribed
rational event rows, TikZ coordinate substitution, and the finite ledger. It is
not an interpreter, collision scheduler, simulator, or theorem prover.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import os
import re
import stat
import argparse

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--release', required=True, type=Path)
ap.add_argument('--physical-source', required=True, type=Path)
ap.add_argument('--arithmetic-source', required=True, type=Path)
ap.add_argument('--prior-physical-snapshot', required=True, type=Path)
ap.add_argument('--prior-arithmetic-snapshot', required=True, type=Path)
ap.add_argument('--output-dir', required=True, type=Path)
args = ap.parse_args()
for p in vars(args).values():
    if not p.is_absolute() or p != p.resolve():
        raise ValueError('Absolute nonsymlink paths are required')
OUT = args.output_dir
MAN = args.release / 'manuscript'
ROOTS = {
    'physical': args.physical_source,
    'arithmetic': args.arithmetic_source,
}
for protected in [args.release, *ROOTS.values(), Path(__file__).resolve().parent]:
    if OUT == protected or OUT in protected.parents or protected in OUT.parents:
        raise ValueError('Output overlaps a protected input or checker tree')
if OUT.exists():
    raise ValueError('Output directory must be new')
PINS = {
    'physical': '85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f',
    'arithmetic': '5d9d7de3c9b6ca5551d7cd537b0e3570c0272af6716ba814453d5ad2123aea6a',
}

def read(p):
    with os.fdopen(os.open(p, os.O_RDONLY | os.O_NOFOLLOW | os.O_NOATIME), 'rb') as f:
        return f.read()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def snapshot(root):
    ans = {}
    for p in sorted(root.rglob('*')):
        s = p.lstat()
        if not stat.S_ISREG(s.st_mode) and not stat.S_ISDIR(s.st_mode):
            raise ValueError('Nonregular source entry: ' + str(p))
        item = {'mode': oct(s.st_mode), 'size': s.st_size, 'mtime_ns': s.st_mtime_ns}
        if p.is_file():
            item['sha256'] = digest(read(p))
        ans[str(p.relative_to(root))] = item
    return ans

checks = []
def check(name, ok, detail=None):
    checks.append({'name': name, 'pass': bool(ok), 'detail': detail})
    if not ok:
        raise AssertionError(name + ': ' + str(detail))

before = {name: snapshot(root) for name, root in ROOTS.items()}
for name, root in ROOTS.items():
    check('frozen proof pin ' + name, digest(read(root / 'PROOF.md')) == PINS[name])
histories = {
    'physical': args.prior_physical_snapshot,
    'arithmetic': args.prior_arithmetic_snapshot,
}
for name, p in histories.items():
    old = json.loads(read(p))
    for rel, now in before[name].items():
        if rel not in old:
            continue
        for field in ('mode', 'size', 'mtime_ns', 'sha256'):
            if field in now:
                check('prior freeze ' + name + '/' + rel + ' ' + field, now[field] == old[rel][field])

tex = {p.name: read(p).decode('utf-8') for p in sorted(MAN.glob('*.tex'))}
manifest = snapshot(MAN)
def compact(s):
    return re.sub(r'\s+', '', s)

# Human-reviewed formula and rule transcription anchors. A text hit supports
# transcription only: the mathematical reasoning is separately in AUDIT.md.
needles = {
 'branch.tex': [
  r'X_{\mathrm{pre}}:-\frac12', r'X_{\mathrm{fast}}:+2', r'X_{\mathrm{post}}:-\frac12',
  r'\text{speed}&1&-3/2&1&-1/4&4&-1&-1',
  r'\{Q_0,X_0\}&\ruleto\{Q_1,X_{\mathrm{pre}}\}',
  r'\{Q_1,L\}&\ruleto\{Q_2,L\}',
  r'\{Q_2,X_{\mathrm{pre}}\}&\ruleto\{Q_3,X_{\mathrm{fast}}\}',
  r'\{Q_3,L\}&\ruleto\{Q_4,L\}',
  r'\{X_{\mathrm{fast}},Y\}&\ruleto\{X_{\mathrm{post}},Y\}',
  r'\{Q_4,X_{\mathrm{post}}\}&\ruleto\{C_{\ZZ},X_0\}',
  r'\{Q_4,X_{\mathrm{fast}}\}&\ruleto\{C_{\NN},X_0\}',
  r'B=\frac{35x}{9}', r'A=\frac{17x}{9}+\frac y2', r'A-B=\frac{y-4x}{2}',
  r'F=\frac{10y-8x}{9}',
  r'1 & $x$ & $x$ & $x$', r'2 & $5x/3$ & $0$ & $2x/3$',
  r'3 & $19x/9$ & $4x/9$ & $4x/9$', r'4 & $35x/9$ & $0$ & $4x$',
  r'5 & $17x/9+y/2$ & $2y-8x$ & $y$',
  r'6 & $11x/3+5y/18$ & $F$ & $F$', r'7 & $25(2x+y)/18$ & $0$ & $F$',
  r'5 & $53x/9$ & $8x$ & $8x$', r'6 & $125x/9$ & $0$ & $8x$',
 ],
 'inverse.tex': [
  r'\{C_c,L\}\ruleto\{\overline C_c,L\}',
  r'\{\overline C_{\ZZ},X_0\}&\ruleto\{\overline Q_{4,\ZZ},\overline X_{\mathrm{post},\ZZ}\}',
  r'\{\overline C_{\NN},X_0\}&\ruleto\{\overline Q_{4,\NN},\overline X_{\mathrm{fast},\NN}\}',
  r'\{\overline X_{\mathrm{post},\ZZ},Y\}\ruleto\{\overline X_{\mathrm{fast},\ZZ},Y\}',
  r'\{\overline Q_{4,c},L\}&\ruleto\{\overline Q_{3,c},L\}',
  r'\{\overline Q_{3,c},\overline X_{\mathrm{fast},c}\}&\ruleto\{\overline Q_{2,c},\overline X_{\mathrm{pre},c}\}',
  r'\{\overline Q_{2,c},L\}&\ruleto\{\overline Q_{1,c},L\}',
  r'\{\overline Q_{1,c},\overline X_{\mathrm{pre},c}\}&\ruleto\{\overline Q_{0,c},X_0\}',
  r'\{\overline Q_{0,c},L\}&\ruleto\{Q_{\mathrm{out},c},L\}',
  r'T-t_{m-1},\ T-t_{m-2},\ \ldots,\ T-t_1,\ T',
  r'T_{\mathrm{test},\ZZ}=\frac{25(2x+y)}9', r'T_{\mathrm{test},\NN}=\frac{250x}{9}',
 ],
 'updates.tex': [
  r'h=\frac{k-1}{k+1}', r'(t,t),\quad(2t,0),\quad(2t+kt,kt),\quad(2t+2kt,0)',
  r'0<t<s<D,\qquad0<kt<s', r'0<t<s<D,\qquad0<t+eD<s',
  r'u=\frac{t}{1-e}', r'h=\frac e{2-e}',
  r'\{K_0,M_0\}&\ruleto\{K_1,M_h\}', r'\{K_1,A\}&\ruleto\{K_2,A\}',
  r'\{K_2,M_h\}&\ruleto\{K_3,M_0\}', r'\{K_3,A\}&\ruleto\{K_{\mathrm{out}},A\}',
  r'\{V_0,M_0\}&\ruleto\{V_1,M\prime_h\}',
  r'\{V_1,S\}&\ruleto\{V_2,S\}', r'\{V_2,B\}&\ruleto\{V_3,B\}',
  r'\{V_3,S\}&\ruleto\{V_4,S\}',
  r'\{V_4,M\prime_h\}&\ruleto\{V_5,M_0\}',
  r'\{V_5,A\}&\ruleto\{V_{\mathrm{out}},A\}',
  r't\ \longmapsto\ \frac t2\ \longmapsto\ \frac t2+\frac D{40}',
  r't\ \longmapsto\ 2t\ \longmapsto\ 2t-\frac D{20}',
  r'T_{\mathrm{inc}}&=2D+\frac{196}{39}t', r'T_{\mathrm{dec}}&=2D+\frac{290}{21}t',
 ],
 'certificate.tex': [
  r'E=I+2C+1,\qquad Z=C', r'T(E+2)', r'T(E+Z+4)+1',
  r'S_{t,e}&=(w_{t,e}-1)(w_{t,e}-2)', r'O_t&=\sum_e s_{t,e}-1',
  r'U_t&=A_{t+1}-A_t-\sum_e d_e s_{t,e}',
  r'V_t&=B_{t+1}-B_t-\sum_e f_e s_{t,e}',
  r's_{t,e}(A_t-1)', r's_{t,e}(B_t-1)',
  r'C_{\mathrm{initial}}&=\sum_e u_e s_{0,e}-q_0',
  r'C_t&=\sum_e v_e s_{t,e}-\sum_e u_e s_{t+1,e}',
  r'C_{\mathrm{final}}&=\sum_e v_e s_{T-1,e}-H',
  r'P_{M,T}=\sum_{r\in\mathcal R}r^2', r'H_{\mathrm{early}}=\sum_{t=0}^{T-1}s_{t,h}',
  r'P_{M,0}=(q_0-H)^2', r'T(E+Z+4)+2', r'T(I+2C+3)', r'T(I+3C+5)+1',
  r'2^{-(A-1)}', r'2^{-(B-1)}',
 ],
}
for filename, literals in needles.items():
    # Prime syntax is intentionally normalized, without evaluating TeX.
    text = compact(tex[filename].replace("M'_h", r'M\prime_h'))
    for number, needle in enumerate(literals, 1):
        check(filename + ' formula/rule anchor ' + str(number), compact(needle) in text, needle)

# Linear forms in (x,y), used only to check the supplied rows and not to choose
# collision partners. The two chamber rows are manually transcribed.
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def mul(k,a): return tuple(k*x for x in a)
def sub(a,b): return add(a,mul(-1,b))
def lin(a=0,b=0): return (F(a),F(b))
zero, x, y = lin(),lin(1),lin(0,1)
common = [
 (zero,zero,x), (x,x,x), (mul(F(5,3),x),zero,mul(F(2,3),x)),
 (mul(F(19,9),x),mul(F(4,9),x),mul(F(4,9),x)),
 (mul(F(35,9),x),zero,mul(4,x)),
]
fx = add(mul(F(-8,9),x),mul(F(10,9),y))
tables = {
 'Z': common + [(add(mul(F(17,9),x),mul(F(1,2),y)), add(mul(-8,x),mul(2,y)),y),
               (add(mul(F(11,3),x),mul(F(5,18),y)),fx,fx),
               (add(mul(F(25,9),x),mul(F(25,18),y)),zero,fx)],
 'N': common + [(mul(F(53,9),x),mul(8,x),mul(8,x)),(mul(F(125,9),x),zero,mul(8,x))],
}
velocities = {
 'Z': [(1,0),(F(-3,2),F(-1,2)),(1,F(-1,2)),(F(-1,4),2),(4,2),(4,F(-1,2)),(-1,0)],
 'N': [(1,0),(F(-3,2),F(-1,2)),(1,F(-1,2)),(F(-1,4),2),(4,2),(-1,0)],
}
for branch, rows in tables.items():
    for i, ((ta,qa,xa),(tb,qb,xb),(vq,vx)) in enumerate(zip(rows,rows[1:],velocities[branch]),1):
        dt = sub(tb,ta)
        check(branch + ' row ' + str(i) + ' messenger identity', sub(qb,qa)==mul(vq,dt))
        check(branch + ' row ' + str(i) + ' target identity', sub(xb,xa)==mul(vx,dt))

# Extract only explicit numeric TikZ polyline coordinates. Fraction parses a
# single rational/decimal token; neither Python eval nor TeX evaluation is used.
draws = re.findall(r'\\draw\[(target,very thick|messenger,thick)\]\s*([^;]+);',tex['inverse.tex'])
draws = [(style,body) for style,body in draws if body.count('--') > 1]
check('four scientific TikZ polylines',len(draws)==4,len(draws))
figure_rows = []
for branch, initial in [('Z',(F(3,20),F(9,10))),('N',(F(3,40),F(9,10)))]:
    rows = tables[branch]
    value = lambda v: v[0]*initial[0]+v[1]*initial[1]
    concrete = [(value(t),value(q),value(z)) for t,q,z in rows]
    end = concrete[-1][0]
    complete = concrete + [(2*end-t,q,z) for t,q,z in reversed(concrete[:-1])]
    for role,index in [('target',2),('messenger',1)]:
        item = draws.pop(0)
        check(branch + ' figure role ' + role,item[0].startswith(role))
        coords = [(F(a),F(b)) for a,b in re.findall(r'\(([-.0-9/]+),([-.0-9/]+)\)',item[1])]
        expected = [(row[index],row[0]) for row in complete]
        check(branch + ' ' + role + ' exact coordinate count',len(coords)==len(expected))
        for n,(actual,want) in enumerate(zip(coords,expected)):
            check(branch + ' ' + role + ' rational point '+str(n),actual==want,[list(map(str,actual)),list(map(str,want))])
        figure_rows.append({'branch':branch,'role':role,'points':[[str(a),str(b)] for a,b in coords]})

# Four coefficient identities are enough to check the two affine updates for
# every t: only fixed k,e values are used here, not native counter execution.
for k,e,claimed in [(F(1,2),F(1,40),F(196,39)),(F(2),F(-1,20),F(290,21))]:
    check('update duration coefficient '+str(k),2*(1+k)+2*(k+k/(1-e))==claimed)
    check('translation launch speed '+str(e),(1/(1-e)-1)/(1/(1-e)+1)==e/(2-e))
for T in (1,2,3,7):
    for I,C in ((0,0),(1,0),(0,1),(3,4)):
        E,Z=I+2*C+1,C
        check('residual slot identity '+str((T,I,C)),T*E+T+2*T+T*Z+(T+1)==T*(E+Z+4)+1)
        check('witness ledger '+str((T,I,C)),T*(E+2)==T*(I+2*C+3))
        check('instruction ledger '+str((T,I,C)),T*(E+Z+4)+1==T*(I+3*C+5)+1)

after = {name: snapshot(root) for name, root in ROOTS.items()}
check('frozen source bytes modes nanosecond mtimes preserved',before==after)
check('manuscript unchanged during static check',manifest==snapshot(MAN))
result = {'status':'PASS','check_count':len(checks),'checks':checks,
          'proof_pins':PINS,'manuscript_files':manifest,'figure_rows':figure_rows,
          'checker_sha256':digest(read(Path(__file__))),
          'scope':'Static transcription, supplied-row identities and rational TikZ substitution only; no scientific source executed.'}
OUT.mkdir(mode=0o700)
for name,data in [('static_results.json',result),('frozen_sources_before.json',before),('frozen_sources_after.json',after)]:
    (OUT/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','checks':len(checks),'checker_sha256':result['checker_sha256']}))
