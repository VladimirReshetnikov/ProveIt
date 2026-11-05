#!/usr/bin/env python3
"""Read-only exact row-binding and receipt audit. This does not invoke Lean."""
import hashlib
import json
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def need(condition, reason):
    if not condition:
        raise RuntimeError(reason)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p64 = ROOT/'normalized106-rational66/polynomial.json'
    p65 = ROOT/'fourteen-normalized-product106/polynomial.json'
    source = HERE/'Normalized106Rational66.lean'
    need(digest(source) == '99b0d71b27771ed5416e295f28f6d1668a4c5a7cdbf8a756a7ac19b513129f42', 'source hash')
    need(digest(p64) == '61784a1cdc3594174c3e321712322cebdffff20be51ef7f2bc0feb3b8f9498a4', '64 input hash')
    need(digest(p65) == '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1', '65 input hash')
    a,b = (json.loads(p.read_bytes()) for p in (p64,p65))
    need(a['witnesses'] == b['witnesses'], 'witness order')
    a,b = a['source'],b['source']
    need(len(a) == 66 and len(b) == 67, 'row counts')
    ia = next(i for i,r in enumerate(a) if r[0] == 'q2minus1')
    ib = next(i for i,r in enumerate(b) if r[0] == 'q2minus1')
    ra = next(i for i,r in enumerate(a) if r[0] == 'R')
    rb = next(i for i,r in enumerate(b) if r[0] == 'R')
    need(a[:ia] == b[:ib] and a[ra+1:] == b[rb+1:], 'shared graph regions')
    text = source.read_text()
    sections = {}
    for name, nxt in [('head','rank66'),('rank66','rank67'),('rank67','suffix'),('suffix','value66')]:
        sections[name] = text.split('\ndef '+name+' ',1)[1].split('\ndef '+nxt+' ',1)[0]
    rowpat = re.compile(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$', re.M)
    expected = {'head': a[:ia], 'rank66': a[ia:ra+1], 'rank67': b[ib:rb+1], 'suffix': a[ra+1:]}
    for name, rows in expected.items():
        got = [[name, op, int(x) if x.isdigit() else x, int(y) if y.isdigit() else y]
               for name,x,op,y in rowpat.findall(sections[name])]
        need(got == rows, name+' literal row mismatch')
    fields = [r[0] for r in a[:ia]]
    struct = text.split('\nstructure Head ',1)[1].split('\ndef head ',1)[0]
    need(re.findall(r'^  (\w+) : R$',struct,re.M) == fields, 'head fields')
    need('  ⟨'+', '.join(fields)+'⟩' in sections['head'], 'head constructor')
    for name in ('head','rank66','rank67','suffix'):
        body = sections[name]
        used = {str(x) for r in expected[name] for x in r[2:]}
        if name in ('head','suffix'):
            witness = json.loads(p64.read_bytes())['witnesses']
            inputs = [(x,f'v {i}') for i,x in enumerate(witness)]
            inputs += [(x,f'p {i}') for i,x in enumerate(('beta','K0','MC','MF'))]
            for key, val in inputs:
                if key in used:
                    need(f'  let {key} := {val}\n' in body, name+' input alias '+key)
        if name != 'head':
            for field in fields:
                if field in used:
                    need(f'  let {field} := h.{field}\n' in body, name+' field alias '+field)
    need('  let R := rank\n' in sections['suffix'], 'rank alias')
    print('PASS exact 28+5+33 / 28+6+33 source-to-graph rows and aliases; no Lean replay')

if __name__ == '__main__':
    main()
