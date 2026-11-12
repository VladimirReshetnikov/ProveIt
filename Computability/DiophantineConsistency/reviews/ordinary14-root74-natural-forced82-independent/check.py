#!/usr/bin/env python3
"""Independent structural and arithmetic controls; not an iPRA proof."""
import hashlib, json, math
from pathlib import Path

root = Path(__file__).resolve().parents[2]
p = root / 'research/ordinary14-root74-natural-forced82/candidate.json'
q = root / 'research/ordinary14-root74-natural-cancel85/candidate.json'
raw, oldraw = p.read_bytes(), q.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'
assert hashlib.sha256(oldraw).hexdigest() == '24a5ddfdabeae36eb40867239fdc5dfd53ba60d611f0e83268ffb9bfbac85957'
a, b = json.loads(raw), json.loads(oldraw)
replacement = {'f': 'n_f', 'r': 'n_r', 'y': 'n_y'}
old = {row[0]: row[1:] for row in b['source']}
new = {row[0]: row[1:] for row in a['source']}
assert len(old) == 85 and len(new) == 82
assert set(old) - set(new) == set(replacement) and set(new) <= set(old)
for name, var in replacement.items():
    assert old[name] == ['+', var, 1]
for name, row in new.items():
    op, left, right = old[name]
    assert row == [op, replacement.get(left, left), replacement.get(right, right)]
# Check the algebraic shapes used in the hand proof against the graph itself.
expected = {
 'q':['+',1,'qm'], 'X':['*','q','w'], 'Y':['*','q3','s'],
 'E':['*','X','Y'], 'k':['+','kbase',1], 'kY':['*','Y','k'],
 'ell':['*','E','kY'], 'a':['+','E','Y'], 'H':['+',3,'g15'],
 'g15':['*',4,'a'], 'g17':['*','a','a'], 'Delta':['+','H','g17'],
 'f2':['*','n_f','n_f'], 'rho':['-','f2',1], 'Q':['*','Delta','rho'],
 'I':['*','c2','i'], 'g71':['*','I','I'], 'g72':['-','g71','Q'],
 'Fs':['+',1,'g72'], 'g38':['*','n_r','n_r'], 'g30':['+','ell','k'],
 'g40':['*','ell','g30'], 'F0':['-','g38','g40'],
 'y2':['*','n_y','n_y'], 'V2':['*','V','V'], 'g81':['-','y2','V2'],
 'g82':['*','Q','g81'], 'Fa':['-','y2','g82'],
 'g61':['*','Dstar','Dstar'], 'g62':['*','U','U'],
 'c2':['*','c','c'], 'g63':['*','Delta','c2'], 'g64':['+',1,'g63'],
 'g65':['*','g62','g64'], 'A1':['-','g61','g65'], 'F1':['+',1,'A1'],
 'P01':['*','F0','F1'], 'P012':['*','P01','Fa'],
 'P0123':['*','P012','Fs'], 'P01234':['*','P0123','guard'],
 'out':['-','P01234',1],
}
for name, row in expected.items(): assert new[name] == row, name
# Exhaust the residues relevant to the unit-factor exclusions.
squares = {i*i % 4 for i in range(4)}
assert squares == {0,1}
for a0 in range(4):
    delta = (a0*a0 + 4*a0 + 3) % 4
    assert delta in (0,3)
    for f in range(4):
        Q = delta*(f*f-1) % 4
        assert Q in (0,1)
        for y in range(4):
            for v in range(4):
                assert (y*y-Q*(y*y-v*v)) % 4 != 3
        for c in range(4):
            for u in range(4):
                for d in range(4):
                    assert (1+d*d-u*u*(1+delta*c*c)) % 4 != 3
        for i in range(4): assert (1+i*i-Q) % 4 != 3
# Finite controls only for the separately proven negative-Pell exclusion.
for m in range(2,31):
    for k in range(1,201):
        n = m*(m+1)*k*k-1
        assert math.isqrt(n)**2 != n
print(json.dumps({'scope':'independent structural and residue controls; unbounded reasoning remains a mathematical proof, not Lean', 'gates':len(new), 'removed_shifts':sorted(replacement), 'shape_checks':len(expected), 'modulus':4, 'bounded_pell_controls':29*200},sort_keys=True,indent=2))
