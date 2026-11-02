#!/usr/bin/env python3
"""Concrete cyclic-index and payload-slice checks; does not run Lean."""
import json
P=8807
indices=0
for N in range(1,9):
    for s in range(N):
        for h in range(N):
            for u in range(9):
                k=P*h+1013+u
                assert (k-30)%(P*N)==P*h+983+u
                assert (k-P*s)%(P*N)==P*((h-s)%N)+1013+u
                indices+=1
            for u in range(8):
                k=P*h+1065+u
                assert (k-62)%(P*N)==P*h+1003+u
                assert (k-8849)%(P*N)==P*((h-1)%N)+1023+u
                indices+=1
fields=0
for w in (0,1,254,255):
    for n in (0,1,510,511):
        for e in (0,1,254,255):
            for s in (0,1,510,511):
                v=w+2**8*n+2**17*e+2**25*s+127*2**34
                assert ((v>>25)&511,(v>>8)&511,(v>>17)&255,v&255)==(s,n,e,w)
                fields+=1
print(json.dumps({'cyclic_bit_index_cases':indices,'standard_N_range':[1,8],
                  'payload_field_cases':fields,'lean_launched':False},indent=2,sort_keys=True))
