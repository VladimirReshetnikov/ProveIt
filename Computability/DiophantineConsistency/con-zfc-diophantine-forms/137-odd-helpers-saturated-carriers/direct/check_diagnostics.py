#!/usr/bin/env python3
"""Finite diagnostics only; the audit proof supplies unbounded conclusions."""
import json

def need(b, message):
    if not b:
        raise ValueError(message)

def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x + (a*a-1)*y, x+a*y
    return x, y

count = 0
bits = 0
for a in range(2, 6):
    for W in (2, 4):
        U, C = pell(a, W)
        H, J = pell(U, C)
        need(U % 2 == 1 and C % 2 == 0 and H % 2 == 1, 'even-index parity')
        J *= C
        need(H*H-(a*a-1)*J*J == 1, 'Pell composition')
        need(J % (C*C) == 0 and J//(C*C) % 2 == 1, 'odd square quotient')
        for asgn in (-1, 1):
            for usgn in (-1, 1):
                for csgn in (-1, 1):
                    A, actualU, actualC = asgn*a, usgn*U, csgn*C
                    # Choose the complete positive-base replacement helper.
                    D = A + H * (((1-A)*pow(H, -1, 4*J)) % (4*J))
                    while D < 5:
                        D += 4*H*J
                    S, R = pell(D, W)
                    S *= usgn
                    need((D-A) % H == 0 and (D-1) % (4*J) == 0, 'full helper CRT')
                    need((S-actualU) % H == 0 and (R-W) % (4*actualC) == 0, 'signed cap restoration')
                    need(S*S-(D*D-1)*R*R == 1, 'comparison norm')
                    need(actualU*actualU-(A*A-1)*actualC*actualC == 1, 'unchanged signed cap')
                    bits = max(bits, S.bit_length())
                    count += 1

base_minus_three = []
for J in range(-20, 21):
    for d in range(-20, 21):
        if 1+4*J*(d+1) != -3:
            continue
        # The full equation forces J*(d+1)=-1, hence |J|=1.
        need(abs(J) == 1, 'D=-3 integer factorization')
        candidates = [C for C in range(-20, 21) if C != 0 and J % (C*C) == 0 and (J//(C*C)) % 2 == 1]
        need(all(abs(C) == 1 for C in candidates), 'D=-3 collapsed cap only')
        base_minus_three.append({'J': J, 'd': d, 'possible_C': candidates, 'excluded_by': 'quadratic cap plus nonzero-target pooled congruence'})

support_cases = 0
for q in range(1, 8):
    for u in range(-12, 13):
        for v in range(-12, 13):
            if u*v >= 0 and q*u+v > 0:
                need(u >= 0 and v >= 0, 'support product sign lemma')
                support_cases += 1

print(json.dumps({'status':'PASS', 'finite_only':True, 'complete_signed_helper_restorations':count, 'maximum_comparison_abscissa_bits':bits, 'D_minus_three_cases':base_minus_three, 'support_sign_cases':support_cases}, indent=2, sort_keys=True))
