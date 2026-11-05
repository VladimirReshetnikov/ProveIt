#!/usr/bin/env python3
"""Finite controls, not proof of graph-zero existence or conversion."""
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
rigidity=0
for X in range(1,13):
  for Y in range(1,13):
    U=Y*Y; a=(X+1)*Y; H=4*a+3
    for c in range(1,13):
      for h1 in range(1,13):
        A=U*(X+a*c)+H*h1
        for h2 in range(1,13):
          B=U*(X+a*c)+H*h2
          if ((A*A==B*B) != (h1==h2)):
            raise ValueError('positive root rigidity')
          rigidity+=1
controls=0
for b in range(1,13):
  beta=(1<<b)-1
  for J in range(1,1001):
    q=beta*J+1
    ispower=(q & (q-1))==0
    d=q.bit_length()-1
    repunit=(d%b==0 and J==((1<<d)-1)//beta)
    if ispower!=repunit: raise ValueError(('repunit',b,J))
    controls+=1
if (pow(2,590069,3)-1)%3!=1: raise ValueError('fixed beta residue')
print(json.dumps({'status':'PASS_FINITE_CONTROLS','positive_square_comparisons':rigidity,'repunit_cases':controls,'fixed_beta_mod_3':1,'scope':'bounded arithmetic controls; not graph-zero existence, witness conversion or all-model proof'},sort_keys=True,indent=2))
