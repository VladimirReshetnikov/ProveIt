from pathlib import Path
from hashlib import sha256
import json, math, subprocess, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary10-two-norm-divisible61-independent')
for name,digest in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(name).read_bytes()).hexdigest()==digest, name
P=Path('research/ordinary9-shifted-free-aux-two-norm64')
Q=Path('research/ordinary10-two-norm-divisible61')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(Q/'check.py')])==(Q/'receipt.json').read_bytes()
a=json.loads((P/'candidate.json').read_text()); b=json.loads((Q/'candidate.json').read_text())
assert len(a['witnesses'])==9 and len(a['source'])==64
assert len(b['witnesses'])==10 and len(b['source'])==61
assert a['fixed_numerals']==b['fixed_numerals']==['beta','K0','MC','MF']

def parse(g):
    d={v:('input',v) for v in g['witnesses']+g['fixed_numerals']}
    for n,op,x,y in g['source']:
        assert n not in d and op in '+-*'
        assert isinstance(x,int) or x in d
        assert isinstance(y,int) or y in d
        d[n]=(op,('int',x) if isinstance(x,int) else d[x],('int',y) if isinstance(y,int) else d[y])
    return d
x=parse(a); y=parse(b)
for n in ('A1','Bt','ell','k','qm','g41'):
    assert x[n]==y[n],n
arows={r[0]:r[1:] for r in a['source']}; brows={r[0]:r[1:] for r in b['source']}
expected_old={'g31':['+','g30','n_r'],'folded_kBt':['*','k','Bt'],'folded_g31':['-','g31','folded_kBt'],'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],'g38':['*','Z','Z'],'g39':['*','qm','qm'],'g42':['*','g39','g41'],'A0':['-','g38','g42']}
expected_new={'bh':['*','qm','n_h'],'Bres':['-','Bt','bh'],'tausq':['*','n_tau','n_tau'],'firstres':['-','tausq','g41'],'Bsq':['*','Bres','Bres'],'firstsq':['*','firstres','firstres'],'A1sq':['*','A1','A1'],'sum1':['+','Bsq','firstsq'],'out':['+','sum1','A1sq']}
for key,value in expected_old.items(): assert arows[key]==value
for key,value in expected_new.items(): assert brows[key]==value
# Independent support traversal, including every fixed port and witness.
idx={r[0]:r[1:] for r in b['source']};live=set();leaves=set()
def visit(node):
    if isinstance(node,int): return
    if node not in idx: leaves.add(node); return
    if node in live:return
    live.add(node)
    _,u,v=idx[node]; visit(u);visit(v)
visit(b['output'])
assert len(live)==61 and leaves==set(b['witnesses']+b['fixed_numerals'])
# Independent univariate ray: exact integer polynomial for three beta values.
def add(u,v,sign=1):
    z=u.copy()
    for i,c in v.items():z[i]=z.get(i,0)+sign*c
    return {i:c for i,c in z.items() if c}
def mul(u,v):
    z={}
    for i,c in u.items():
        for j,d in v.items():z[i+j]=z.get(i+j,0)+c*d
    return {i:c for i,c in z.items() if c}
for beta in (1,2,7):
    d={n:{} for n in b['witnesses']+b['fixed_numerals']}
    d['beta']={0:beta}
    for n in ('n_J','n_w','n_s','n_eta','n_gamma'):d[n]={1:1}
    for n,op,u,v in b['source']:
        u={0:u} if isinstance(u,int) and u else {} if isinstance(u,int) else d[u]
        v={0:v} if isinstance(v,int) and v else {} if isinstance(v,int) else d[v]
        d[n]=add(u,v) if op=='+' else add(u,v,-1) if op=='-' else mul(u,v)
    assert max(d['out'])==60 and d['out'][60]==64*beta**42
# Scalar first-norm controls cover both signs whenever their old r is natural.
counts={'+':0,'-':0}
for M in range(1,9):
    X,Y=1,M
    Af=2*M+1; delta=M*(M+1); tau,k=1,0
    for n in range(1,5):
        tau,k=Af*tau+2*delta*k,2*tau+Af*k
        ell=M*k
        assert tau*tau==1+ell*(ell+k) and tau>ell
        for bb in range(1,5):
            for hh in range(1,5):
                B=bb*hh
                for sign in (1,-1):
                    r=sign*tau-ell-k+k*B+hh
                    if r>=0:
                        Z=bb*(ell+k+r-k*B)-B
                        assert Z==sign*bb*tau
                        assert Z*Z==bb*bb*(1+ell*(ell+k))
                        assert B//bb==hh and abs(Z)//bb==tau
                        rr=tau-ell-k+k*bb*hh+hh
                        assert rr>=0 and bb*(ell+k+rr-k*B)-B==bb*tau
                        counts['+' if sign==1 else '-']+=1
assert all(counts.values())
# At X=0 the asserted H>3q^2 holds, independent of the residue data.
for q in range(1,100):
    for s in range(1,10):
        Y=q**3*s; U=Y*q*q; H=4*Y+3
        assert H>3*q*q and (4*U-q*q*(H-3))==0
print(json.dumps({'checked_pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_receipt_reproduced':True,'live_witnesses':10,'live_operations':61,'old_and_new_main_trees_equal':True,'first_root_and_residual_rows_checked':True,'ray_degree_checks_beta':[1,2,7],'scalar_first_norm_controls_by_sign':counts,'x_zero_finite_controls':891,'scope':'standard integers; beta>0 and K0>0; relaxed child only','lean_executed':False},sort_keys=True,indent=2))
