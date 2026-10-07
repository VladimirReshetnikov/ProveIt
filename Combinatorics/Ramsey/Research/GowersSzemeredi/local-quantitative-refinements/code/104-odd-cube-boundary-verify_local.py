#!/usr/bin/env python3
"""Direct integer cube counts for nontrivial examples in the local regime."""
from __future__ import annotations
import itertools as it
import json
from fractions import Fraction as Q
from pathlib import Path
import numpy as np


def require(value: bool, message: str) -> None:
    if not bool(value):
        raise RuntimeError(message)


def cyclic_cube3(n: int, A: list[int]) -> tuple[int,int]:
    """Two successive correlation counts, using no complement polynomial."""
    f = np.zeros(n, dtype=np.int64)
    f[A] = 1
    indices = (np.arange(n)[:,None]+np.arange(n)[None,:]) % n
    corr = (f[indices]*f[None,:]).sum(axis=1)
    energy = int(corr @ corr)
    cubes = 0
    for t in range(n):
        b = f*f[indices[t]]
        cb = (b[indices]*b[None,:]).sum(axis=1)
        cubes += int(cb @ cb)
    return energy,cubes


def main() -> None:
    examples = [
        (127,[0]), (127,[0,1]), (127,[0,2]),
        (251,[0,1,2,3]), (251,[0,1,4,16]),
        (243,[0,81,162]), (243,[0,1,81]),
        (125,[0,25,50,75,100]),
    ]
    rows=[]
    for h,R in examples:
        r=len(R); n=h-r
        A=[i for i in range(h) if i not in R]
        energy,cubes=cyclic_cube3(h,A)
        er,cr=cyclic_cube3(h,R)
        deficit=Q(n**4-cubes,n**4)
        delta=Q(r,n)
        profile=4*delta-10*delta**2+8*delta**3
        T=h**4-8*r*h**3+28*r*r*h*h-44*r**3*h+23*r**4
        require(T-cubes >= (12*h-140*r)*(r**3-er), 'complement remainder')
        require(r**4-cr <= 4*r*(r**3-er), 'cube/energy comparison')
        if delta<=Q(1,50):
            require(deficit>=profile, 'local cubic profile')
        rows.append(dict(h=h,holes=R,n=n,delta=str(delta),
                         in_stated_local_interval=delta<=Q(1,50),
                         cube_count=cubes,energy=energy,
                         profile_gap=str(deficit-profile),
                         hole_energy_defect=r**3-er))
    # An even-order punctured cyclic group violates the proposed odd profile.
    h=64; n=h-1
    _,cubes=cyclic_cube3(h,list(range(1,h)))
    delta=Q(1,n)
    gap=Q(n**4-cubes,n**4)-(4*delta-10*delta**2+8*delta**3)
    require(gap==-2*delta**4, 'two-torsion obstruction')
    # Exact labelled occupancy counts beyond the tiny exhaustive groups.
    h=27
    x,a,b,c=np.indices((h,h,h,h),dtype=np.int16).reshape(4,-1)
    vertices=np.stack([x,(x+a)%h,(x+b)%h,(x+a+b)%h,
                       (x+c)%h,(x+a+c)%h,(x+b+c)%h,(x+a+b+c)%h],axis=1)
    occupancy=[]
    for R in ([0],[0,1],[0,9,18],[0,1,2]):
        f=np.zeros(h,dtype=np.int64); f[R]=1
        hist=np.bincount(f[vertices].sum(axis=1),minlength=9)
        r=len(R); er,cr=cyclic_cube3(h,list(R))
        T=h**4-8*r*h**3+28*r*r*h*h-44*r**3*h+23*r**4
        require(T-int(hist[0])==12*h*(r**3-er)-35*(r**4-cr)
                +int(hist[5]+5*hist[6]+15*hist[7]), 'larger occupancy identity')
        occupancy.append(dict(group='C27',holes=list(R),histogram=[int(v) for v in hist]))
    report=dict(status='PASS',examples=rows,occupancy=occupancy,
                even_order_obstruction=dict(group='C64',holes=[0],odd_profile_gap=str(gap)),
                ratio_obstruction=dict(group='C3',H=[0],D=[1,2],
                                       cube3=81,proposed_bound_without_size_condition=65))
    path=Path(__file__).with_name('local_verification_results.json')
    path.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
