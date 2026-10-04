#!/usr/bin/env python3
"""Independent exact algebra and inert-data review; never execute source code.

Reads the frozen packet and its declared original dependency files as bytes/JSON.
No source import, eval, exec, subprocess, physical-state advancement, next-event
selection, collision simulation, saved physical schedule, or Lean execution.
The ten-event table below is independently derived algebra, compared as affine
line identities only. The 26-rule declaration is inspected as finite strings.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json
import os
import stat
import sympy as s

DEFAULT = '/workspace/shared/compatible-homogeneous-realization63-20261004'
checks = []
def check(name, value):
    if not value:
        raise AssertionError(name)
    checks.append(name)
def eq(name, a, b):
    differences = list(a-b) if isinstance(a, s.MatrixBase) else [a-b]
    check(name, all(s.cancel(v) == 0 for v in differences))
def read(path):
    # Avoid changing access timestamps where Linux permits O_NOATIME.
    fd = os.open(path, os.O_RDONLY | getattr(os, 'O_NOATIME', 0))
    with os.fdopen(fd, 'rb') as stream:
        return stream.read()
def digest(data):
    return hashlib.sha256(data).hexdigest()
def snapshot(root):
    result = []
    for p in [root] + sorted(root.rglob('*')):
        z = p.lstat()
        item = {'path': str(p.relative_to(root)), 'mode': stat.S_IMODE(z.st_mode),
                'mtime_ns': z.st_mtime_ns, 'ctime_ns': z.st_ctime_ns,
                'kind': 'directory' if p.is_dir() else 'file'}
        if p.is_file():
            data = read(p)
            item.update(bytes=len(data), sha256=digest(data))
        result.append(item)
    return result
def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')
def translation(a, b):
    return s.Matrix([[1,0,0],[a,1,0],[b,0,1]])
def rational_matrix(rows):
    return [[F(v) for v in row] for row in rows]
def solve(A, b):
    # Independent Fraction Gauss-Jordan, not the author's matrix-inverse code.
    M = [list(row)+[rhs] for row,rhs in zip(A,b)]
    size = len(M)
    for col in range(size):
        pivot = next((r for r in range(col,size) if M[r][col]), None)
        if pivot is None:
            return None
        M[col],M[pivot] = M[pivot],M[col]
        p = M[col][col]
        M[col] = [v/p for v in M[col]]
        for r in range(size):
            if r != col:
                c = M[r][col]
                M[r] = [v-c*w for v,w in zip(M[r],M[col])]
    return tuple(row[-1] for row in M)
def determinant(K):
    a,b,c = K[0]; d,e,f = K[1]; g,h,i = K[2]
    return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
def lp(K):
    # Variables g1,g2,g3,epsilon; inequalities use <= convention.
    rows = [([-F(i==j) for j in range(3)]+[F(1)],F(0)) for i in range(3)]
    rows += [([-v for v in row]+[F(1)],F(0)) for row in K]
    rows += [([F(0),F(0),F(0),F(-1)],F(0)),
             ([F(0),F(0),F(0),F(1)],F(1))]
    vertices = set()
    for chosen in combinations(rows,3):
        A = [[F(1),F(1),F(1),F(0)]]+[r for r,b in chosen]
        z = solve(A, [F(1)]+[b for r,b in chosen])
        if z is not None and all(sum(a*x for a,x in zip(r,z))<=b for r,b in rows):
            vertices.add(z)
    return sorted(vertices), max((z[3] for z in vertices), default=None)
def gaps(w):
    return (F(1,3)+w[0], F(1,3)+w[1]-w[0], F(1,3)-w[1])
def ceil(v):
    return -((-v.numerator)//v.denominator)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, default=Path(DEFAULT))
    ap.add_argument('--output', type=Path, default=Path(__file__).parent/'evidence')
    ap.add_argument('--archived-source', action='store_true',
                    help='Verify original-source bindings against archived copies; do not open historical absolute paths')
    args = ap.parse_args()
    source, out = args.source.resolve(), args.output.resolve()
    if source == out or source in out.parents or out in source.parents:
        raise ValueError('Output and frozen source must be disjoint directories')
    out.mkdir(parents=True, exist_ok=True)
    before = snapshot(source)
    manifest = json.loads(read(source/'MANIFEST.json'))
    for item in manifest['files']:
        b = read(source/item['path'])
        check('manifest:'+item['path'], len(b)==item['bytes'] and digest(b)==item['sha256'])
    originals = []
    for item in manifest['original_sources']:
        copy_bytes = read(source/item['copy'])
        check('copied dependency binding:'+item['copy'], len(copy_bytes)==item['bytes'] and digest(copy_bytes)==item['sha256'])
        if not args.archived_source:
            p = Path(item['original']); z = p.stat(); b = read(p)
            check('original binding:'+item['copy'], b==copy_bytes)
            originals.append({'path':str(p),'bytes':len(b),'sha256':digest(b),
                              'mode':stat.S_IMODE(z.st_mode),'mtime_ns':z.st_mtime_ns,'ctime_ns':z.st_ctime_ns})
    author = json.loads(read(source/'evidence/static_checks.json'))
    check('author evidence cardinality', author['named_check_count']==len(author['checks'])==98)
    check('author evidence source hash', author['checker_sha256']==digest(read(source/'static_algebra.py')))

    D,t,e,spect = s.symbols('D t e spect')
    u = t/(1-e); end = t+e*D; h = e/(2-e); alpha = 2*t+2*u
    tm = [0,t,2*t,2*t+u,alpha,alpha+u,alpha+spect,alpha+D,
          alpha+2*D-spect,alpha+2*D-end,alpha+2*D]
    q = [0,t,0,u,0,u,spect,D,spect,end,0]
    target = [t,t,t+h*t,u,u,u,u+h*(spect-u),u+h*(D-u),
              u+h*(2*D-spect-u),end,end]
    qspeed = [1,-1,1,-1,1,1,1,-1,-1,-1]
    tspeed = [0,h,h,0,0,h,h,h,h,0]
    flights = [t,t,u,u,u,spect-u,D-spect,D-spect,spect-end,end]
    for i in range(10):
        eq(f'primitive flight {i+1}',tm[i+1]-tm[i],flights[i])
        eq(f'messenger line {i+1}',q[i+1]-q[i],qspeed[i]*(tm[i+1]-tm[i]))
        eq(f'target line {i+1}',target[i+1]-target[i],tspeed[i]*(tm[i+1]-tm[i]))
    for i in (1,3,5,9):
        eq(f'target contact {i}',q[i],target[i])
    eq('positive opening margin',1+h,2/(2-e))
    eq('positive catch margin',1-h,2*(1-e)/(2-e))
    eq('hidden endpoint from start',u-t,e*t/(1-e))
    eq('hidden endpoint from finish',end-u,e*(D-end)/(1-e))
    eq('primitive duration',tm[-1],2*(t+u)+2*D)
    dx,dy,x,y = s.symbols('dx dy x y')
    eq('reflected target sign',D-((D-y)-dy*D),y+dy*D)
    eq('step exact duration',2*(x+x/(1-dx))+2*D+D+
       2*((D-y)+(D-y)/(1+dy))+2*D+D,
       6*D+2*(1+1/(1-dx))*x+2*(1+1/(1+dy))*(D-y))

    # Static generic 26-rule declaration, not a state machine replay.
    # Each tuple gives marker input/output and incoming/outgoing messenger speed.
    events = [('X','XA',1,-1),('L','L',-1,1),('XA','X',1,-1),('L','L',-1,1),
              ('X','XB',1,1),('Y','Y',1,1),('R','R',1,-1),('Y','Y',-1,-1),
              ('XB','X',-1,-1),('L','L',-1,1),
              ('X','X',1,1),('Y','Y',1,1),('R','R',1,-1),
              ('Y','YA',-1,1),('R','R',1,-1),('YA','Y',-1,1),('R','R',1,-1),
              ('Y','YB',-1,-1),('X','X',-1,-1),('L','L',-1,1),('X','X',1,1),
              ('YB','Y',1,1),('R','R',1,-1),
              ('Y','Y',-1,-1),('X','X',-1,-1),('L','L',-1,1)]
    speed = {'L':s.Integer(0),'X':s.Integer(0),'Y':s.Integer(0),'R':s.Integer(0),
             'XA':dx/(2-dx),'XB':dx/(2-dx),'YA':dy/(2+dy),'YB':dy/(2+dy)}
    rules = []
    for j,(a,b,vin,vout) in enumerate(events):
        check(f'rule {j+1} outgoing phase speed',vout==events[(j+1)%26][2])
        # For |dx|,|dy|<=1/6 the positive linear numerator/denominator
        # margins below prove both speeds lie strictly between -1 and +1.
        rules.append({'event':j+1,'input':[f'Q{j}',a],
                      'output':[f'Q{(j+1)%26}',b],
                      'input_speeds':[str(vin),str(speed[a])],
                      'output_speeds':[str(vout),str(speed[b])]})
    check('rule count and distinct inputs',len(rules)==26 and len({tuple(r['input']) for r in rules})==26)
    for label in ('XA','XB','YA','YB'):
        check('temporary pair:'+label,sum(a==label for a,b,vi,vo in events)==1 and
              sum(b==label for a,b,vi,vo in events)==1)
    for marker in ('L','X','Y','R'):
        check('stationary balance:'+marker,sum(a==marker for a,b,vi,vo in events)==
              sum(b==marker for a,b,vi,vo in events))
    eq('left speed lower margin',1+speed['XA'],2/(2-dx))
    eq('left speed upper margin',1-speed['XA'],2*(1-dx)/(2-dx))
    eq('right speed lower margin',1+speed['YA'],2*(1+dy)/(2+dy))
    eq('right speed upper margin',1-speed['YA'],2/(2+dy))
    dump(out/'generic_translation_rules26.json',{'scope':'Inert generic declaration only, not replayed',
         'parameter_domain':'abs(dx),abs(dy)<=1/6; ordered start, X-first corner and finish',
         'rules':rules,'temporary_labels':4,'messenger_labels':26,'stationary_labels':4})

    H=s.Matrix([[s.Rational(1,3),1,0],[s.Rational(1,3),-1,1],[s.Rational(1,3),0,-1]])
    Hi=s.Matrix([[1,1,1],[s.Rational(2,3),-s.Rational(1,3),-s.Rational(1,3)],
                 [s.Rational(1,3),s.Rational(1,3),-s.Rational(2,3)]])
    eq('gap inverse both ways',H*Hi,s.eye(3)); eq('gap inverse reverse',Hi*H,s.eye(3))
    eq('physical gap definition',H*s.Matrix([D,x-D/3,y-2*D/3]),s.Matrix([x,y-x,D-y]))
    p1,p2,q1,q2=s.symbols('p1 p2 q1 q2')
    eq('translation composition',translation(p1,p2)*translation(q1,q2),translation(p1+q1,p2+q2))
    eq('translations determinant',translation(p1,p2).det(),1)
    nn=s.symbols('n0:9'); N=s.Matrix(3,3,nn); p=s.Matrix([1,p1,p2]); v=N*p
    scale=v[0]; qq=(v[1]/scale,v[2]/scale)
    N0=translation(-qq[0],-qq[1])*N*translation(p1,p2)
    eq('fixed-center first column',N0[:,0],s.Matrix([scale,0,0]))
    eq('same top row',N0[0,1:3],N[0,1:3])
    eq('Schur lower block',N0[1:3,1:3],N[1:3,1:3]-s.Matrix(qq)*N[0,1:3])
    eq('physical composite full N',translation(*qq)*N0*translation(-p1,-p2),N)
    eq('lower determinant times scale',scale*N0[1:3,1:3].det(),N.det())

    trans = json.loads(read(source/'evidence/translation_fixtures.json'))
    trans_results=[]
    for idx,fixture in enumerate(trans):
        p=tuple(map(F,fixture['p'])); q=tuple(map(F,fixture['q']))
        m=min(gaps(p)+gaps(q)); delta=tuple(b-a for a,b in zip(p,q))
        n=max(1,ceil(2*max(map(abs,delta))/m)); step=tuple(v/n for v in delta)
        checkpoint=[tuple(p[j]+k*step[j] for j in range(2)) for k in range(n+1)]
        corner=[(p[0]+(k+1)*step[0],p[1]+k*step[1]) for k in range(n)]
        minimum=min(v for z in corner for v in gaps(z))
        check(f'translation fixture {idx} data',n==fixture['n'] and F(fixture['minimum_endpoint_gap'])==m and
              F(fixture['minimum_corner_gap'])==minimum and fixture['event_count']==26*n and
              fixture['guard_rows']==6*n+3 and fixture['temporary_labels']==4*n)
        check(f'translation fixture {idx} margins',min(v for z in checkpoint for v in gaps(z))>=m and
              minimum>=m/2 and max(map(abs,step))<=m/2<=F(1,6))
        for z,c in zip(checkpoint,corner):
            xx=F(1,3)+z[0]; yy=F(2,3)+z[1]; xx1=F(1,3)+c[0]
            rr=1-yy; rr1=rr-step[1]
            check(f'translation fixture {idx} internal endpoints {len(trans_results)}:'+str(z),
                  0<min(xx,xx1)<=xx/(1-step[0])<=max(xx,xx1)<yy and
                  0<min(rr,rr1)<=rr/(1+step[1])<=max(rr,rr1)<1-xx1)
        trans_results.append({'fixture':idx,'n':n,'minimum_corner_gap':str(minimum)})
    check('all 36 translation fixtures',len(trans)==36)

    lp_results=[]
    for fixture in json.loads(read(source/'evidence/exact_lp_fixtures.json')):
        K=rational_matrix(fixture['matrix']); vertices,best=lp(K)
        expected=None if fixture['optimum'] is None else F(fixture['optimum'])
        check('LP optimum:'+fixture['name'],best==expected)
        check('LP determinant:'+fixture['name'],determinant(K)==F(fixture['determinant']))
        check('LP stored vertex:'+fixture['name'], fixture['vertex'] is None if best is None else
              tuple(map(F,fixture['vertex'])) in vertices and F(fixture['vertex'][3])==best)
        lp_results.append({'name':fixture['name'],'optimum':None if best is None else str(best),
                           'distinct_vertex_count':len(vertices),'vertices':[list(map(str,z)) for z in vertices]})
    # Independent additional boundary, rational, and scale fixtures.
    for K,expected in [([[0,0,0]]*3,F(0)),([[F(1,1000),0,0],[0,F(1,1000),0],[0,0,F(1,1000)]],F(1,3000)),
                       ([[0,-1,0],[0,0,-1],[-1,0,0]],None),
                       ([[1,0,0],[0,1,0],[0,0,0]],F(0))]:
        _,best=lp(rational_matrix(K)); check('additional LP fixture:'+str(K),best==expected)
    dump(out/'independent_lp_vertices.json',lp_results)
    dump(out/'independent_translation_fixtures.json',trans_results)

    K=s.Matrix([[1,1,1],[1,2,1],[1,1,3]])
    worked=Hi*K*H; want=s.Matrix([[4,-1,-1],[-s.Rational(1,3),s.Rational(1,3),s.Rational(1,3)],
            [-s.Rational(1,3),-s.Rational(1,3),s.Rational(5,3)]])
    eq('positive matrix centered conjugate',worked,want)
    eq('positive matrix determinant',K.det(),2)
    z=s.symbols('z'); poly=z**3-6*z**2+8*z-2
    eq('positive matrix cubic',(z*s.eye(3)-K).det(),poly)
    check('positive matrix no rational root',all(poly.subs(z,r)!=0 for r in (-2,-1,1,2)))
    eq('worked normalized middle',translation(s.Rational(1,12),s.Rational(1,12))*worked,
       s.Matrix([[4,-1,-1],[0,s.Rational(1,4),s.Rational(1,4)],[0,-s.Rational(5,12),s.Rational(19,12)]]))
    eq('worked suffix actual final positions',s.Matrix([4,s.Rational(4,3)-s.Rational(4,12),
          s.Rational(8,3)-s.Rational(4,12)]),s.Matrix([4,1,s.Rational(7,3)]))
    E=s.Matrix([[1,0,0],[0,1,0],[-1,0,1]]); A=E-s.eye(3)
    eq('escape nilpotent',A*A,s.zeros(3)); n=s.symbols('n')
    eq('escape induction',E*(s.eye(3)+n*A),s.eye(3)+(n+1)*A)

    after=snapshot(source)
    check('frozen source objects and metadata unchanged',before==after)
    for old in originals:
        p=Path(old['path']); z=p.stat(); b=read(p)
        check('original metadata unchanged:'+p.name,old=={'path':str(p),'bytes':len(b),'sha256':digest(b),
              'mode':stat.S_IMODE(z.st_mode),'mtime_ns':z.st_mtime_ns,'ctime_ns':z.st_ctime_ns})
    dump(out/'frozen_before.json',before); dump(out/'frozen_after.json',after)
    dump(out/'original_bindings.json',originals)
    result={'result':'PASS','named_check_count':len(checks),'checks':checks,
            'checker_sha256':digest(read(Path(__file__))), 'sympy_version':s.__version__,
            'proof_sha256':digest(read(source/'PROOF.md')),
            'historical_original_files_checked':not args.archived_source,
            'boundary':'Independent exact symbolic identities, finite JSON/string comparisons, rational endpoint and LP vertex arithmetic only; no author code, physical simulation, schedule replay or Lean.'}
    dump(out/'independent_checks.json',result)
    print(json.dumps({k:result[k] for k in ('result','named_check_count','checker_sha256')}))

if __name__=='__main__':
    main()
