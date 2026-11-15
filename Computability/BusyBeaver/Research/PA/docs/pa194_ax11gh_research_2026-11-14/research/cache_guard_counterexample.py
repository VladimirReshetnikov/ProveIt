#!/usr/bin/env python3
"""Exact arithmetic witness against caching a then retaining the old guard.
This is a regression check of the finite calculations in the accompanying
universal soundness counterexample; it is not a consistency decision.
"""
import json

def pair(a,b): return (a+b)*(a+b+1)//2+b

def bit(s,z): return bool((s>>z)&1)

a,b,c=0,1,0
m=4*pair(a,b)+1
old=(c!=a and c!=b)
new=(c!=m and c!=b)
assert m==9 and not old and new
assert bit(2,1) and not bit(0,1)
print(json.dumps(dict(status='PASS',parameters=[a,b,c],cached_atom_code=m,
 old_guard=old,incorrect_cached_guard=new,initial_assignment={'x_0':2,'x_1':1},
 membership_antecedent=bit(2,1),universal_counterexample={'x_0':0,'x_1':1},
 counterexample_membership=bit(0,1),
 conclusion='The incorrectly enabled gate contains a false membership-vacuity conjunct.'),indent=2))
