#!/usr/bin/env python3
"""Finite Boolean verification of the schematic Brouwer/UI obstruction.

This is not a PA-conistency certificate. It verifies the algebraic facts
used by the explicit recursive numerical interpretation in the note.
"""
from itertools import product
I=lambda a,b:(not a)or b
F=True
N=lambda a:I(a,F)
U=lambda a:a
EX=lambda a:N(U(N(a)))
rho=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))
for vals in product([False,True],repeat=4):
 a,b,c,u=vals
 assert rho(a,b,c,u)
 assert I(U(a),I(U(I(a,b)),U(b)))
 assert I(U(U(a)),U(U(a)))
 assert I(a,U(a))
 assert I(a,U(EX(a)))
 assert I(U(a),a)
 assert I(a,I(False,b))
 assert I(False,I(a,b))
 assert EX(False)
 assert N(I(a,b))
assert not I(EX(U(False)),False)
assert not I(F,False)
print('PASS: all common schemas, diagonal, positive B and UI hold; old first head and explosion fail.')
