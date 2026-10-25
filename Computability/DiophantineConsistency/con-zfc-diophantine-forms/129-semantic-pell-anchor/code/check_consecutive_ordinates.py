#!/usr/bin/env python3
"""Finite boundary controls; the unbounded proof is in the adjoining note."""
import json

def demand(p,m):
    if not p: raise ValueError(m)

def pell(A,n):
    x,y=1,0
    for _ in range(n): x,y=A*x+(A*A-1)*y,x+A*y
    return x,y

canonical=0
for A in range(2,31):
    for k in range(1,21):
        x,y=pell(A,k)
        _,z=pell(A,k-1)
        demand(y*y+z*z-2*A*y*z==1,'consecutive norm')
        demand(x==A*y-z,'root restoration')
        for n in range(1,A):
            demand(n*y-z>0,'support positivity')
            demand(n*y-z==x+(n-A)*y,'output identity')
            canonical+=1
finite=0
for A in range(2,11):
    for y in range(121):
        for z in range(121):
            if y*y+z*z-2*A*y*z != 1: continue
            for n in range(1,A):
                if n*y-z<0: continue
                demand(0<=z<y,'orientation')
                x=A*y-z
                demand(x>0 and x*x-(A*A-1)*y*y==1,'recovered norm')
                finite+=1
# Remove n<A: an actual counterexample, not merely a failed check.
A,n,y,z=2,4,1,4
demand(y*y+z*z-2*A*y*z==1 and n*y-z==0 and z>y,'negative control')
print(json.dumps({'status':'PASS','canonical_output_checks':canonical,
                  'bounded_orientation_instances':finite,
                  'missing_n_lt_A_counterexample':[A,n,y,z],
                  'scope':'finite controls only; theorem proved separately'},indent=2))
