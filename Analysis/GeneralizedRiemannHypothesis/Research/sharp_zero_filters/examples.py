#!/usr/bin/env python3
"""Illustrative floating-point positive Fourier-jet filters; not certificates.

Run: python examples.py
Requires numpy, scipy, mpmath. Writes examples.json in this directory.
The proof in paper.tex is independent of every numerical result here.
"""
import json
import math
from pathlib import Path
import mpmath as mp
import numpy as np
from scipy.optimize import linprog

mp.mp.dps = 40


def beta_hardy(t):
    s = mp.mpf('0.5') + 1j*t
    phase = mp.im((s+1)/2*mp.log(4/mp.pi) + mp.loggamma((s+1)/2))
    return mp.re(mp.exp(1j*phase)*mp.dirichlet(s, [0, 1, 0, -1]))


def beta_sign_changes(max_height=25):
    """Approximate sign-changing roots only; not a complete zero count."""
    out=[]
    left=mp.mpf('0'); fleft=beta_hardy(left)
    for k in range(1, int(2*max_height)+1):
        right=mp.mpf(k)/2; fright=beta_hardy(right)
        if fleft*fright < 0:
            root=mp.findroot(beta_hardy, (left,right), solver='anderson')
            assert left < root < right and abs(beta_hardy(root)) < mp.mpf('1e-25')
            out.append(root)
        left, fleft = right, fright
    return out


def test_mesh(jets, H, grid_size=1001):
    # p_j is total mass of the symmetric pair at + and - radius_j.
    grid=np.linspace(0,H,grid_size)
    rows=[np.ones(grid_size)]
    for gamma,k in jets:
        rows.append((grid/H)**k*np.cos(float(gamma)*grid+k*np.pi/2))
    matrix=np.vstack(rows)
    rhs=np.zeros(len(rows)); rhs[0]=1
    sol=linprog(np.zeros(grid_size),A_eq=matrix,b_eq=rhs,bounds=(0,None),
                method='highs',options={'primal_feasibility_tolerance':1e-9,
                                         'dual_feasibility_tolerance':1e-9})
    if not sol.success:
        return None
    weights=np.maximum(sol.x,0); weights/=weights.sum()
    residual=float(np.max(np.abs(matrix@weights-rhs)))
    if residual>5e-9:
        return None
    atoms=[(float(x),float(w)) for x,w in zip(grid,weights) if w>0]
    # Independent high-precision evaluation at the approximate input ordinates.
    jet_errors=[]
    for gamma,k in jets:
        value=mp.fsum(mp.mpf(w)*mp.mpf(x)**k*mp.cos(gamma*mp.mpf(x)+k*mp.pi/2)
                      for x,w in atoms)
        jet_errors.append(abs(value))
    return {'half_width':H, 'grid_size':grid_size, 'pairs':len(atoms),
            'max_normalized_lp_residual':residual,
            'max_unscaled_jet_residual_at_approximate_ordinates':float(max(jet_errors,default=0)),
            'mass_residual':float(abs(mp.fsum(mp.mpf(w) for _,w in atoms)-1)),
            'atoms':[{'radius':x,'total_pair_weight':w} for x,w in atoms]}


def demo(name, groups):
    # group = (approximate positive ordinate, target multiplicity)
    jets=[(g,k) for g,m in groups for k in range(m)]
    B=float(max(g for g,m in groups))
    # Discrete approximate Jensen lower bound, for orientation only.
    lower=math.pi/B*sum(m*math.log(B/float(g)) for g,m in groups)
    conservative=0.5*math.log(256*(2*len(jets)+1))
    # This conservative width is a rigorous existence width for one zeta copy,
    # not automatically for arbitrary test groups. Start wide for all examples.
    hi=max(1.0,2*conservative); lo=0.01
    best=test_mesh(jets,hi)
    if best is None:
        raise RuntimeError(f'No numerical witness at initial width for {name}')
    # Feasibility on different meshes is not necessarily monotone. This is a
    # heuristic width search, not a rigorous bracket on the optimum.
    for _ in range(15):
        mid=(lo+hi)/2
        trial=test_mesh(jets,mid)
        if trial is None: lo=mid
        else: hi=mid; best=trial
    best.update({'example':name,'largest_input_ordinate':B,
                 'jensen_lower_bound_for_input_ordinates':lower,
                 'constraints':len(jets),
                 'input_ordinates':[{'gamma':mp.nstr(g,36),'order':m} for g,m in groups]})
    return best


def main():
    z=[mp.im(mp.zetazero(k)) for k in range(1,11)]
    b=beta_sign_changes(25)
    cases=[('zeta_first_1',[(g,1) for g in z[:1]]),
           ('zeta_first_5',[(g,1) for g in z[:5]]),
           ('zeta_first_10',[(g,1) for g in z]),
           ('zeta_first_5_double_jets',[(g,2) for g in z[:5]]),
           ('beta_sign_changes_below_25',[(g,1) for g in b]),
           ('mixed_zeta_and_beta_sample',[(g,1) for g in z if g<25]+[(g,1) for g in b])]
    report={'status':'floating-point illustrations only; no exact zeros or completeness certified',
            'method':'nonnegative linear-program weights on equispaced radii, heuristic width search',
            'versions':{'mpmath':mp.__version__,'numpy':np.__version__},
            'examples':[demo(name,groups) for name,groups in cases]}
    path=Path(__file__).with_name('examples.json')
    path.write_text(json.dumps(report,indent=2)+'\n')
    for e in report['examples']:
        print(f"{e['example']:<32} H={e['half_width']:.6f} pairs={e['pairs']:2d} residual={e['max_unscaled_jet_residual_at_approximate_ordinates']:.2e}")

if __name__=='__main__': main()
