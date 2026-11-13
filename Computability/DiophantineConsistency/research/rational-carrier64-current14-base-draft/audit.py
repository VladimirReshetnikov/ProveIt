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
OUT = Path('/tmp/rational-carrier64-current14-base-priority-check04')

def need(condition, reason):
    if not condition:
        raise RuntimeError(reason)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p64 = ROOT/'rational-carrier64-independent/polynomial.json'
    p65 = ROOT/'rational-carrier64-independent/source/parent65.json'
    source = HERE/'RationalCarrier64Current.lean'
    need(digest(source) == 'beb7b4e898dddb4f0c8bbf1fcccd24b7d57e56df5b48e53c76754c6d51776ec1', 'source hash')
    need(digest(p64) == '8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27', '64 input hash')
    need(digest(p65) == '408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff', '65 input hash')
    a,b = (json.loads(p.read_bytes()) for p in (p64,p65))
    need(a['witnesses'] == b['witnesses'], 'witness order')
    a,b = a['source'],b['source']
    need(len(a) == 64 and len(b) == 65, 'row counts')
    ia = next(i for i,r in enumerate(a) if r[0] == 'q2minus1')
    ib = next(i for i,r in enumerate(b) if r[0] == 'q2minus1')
    ra = next(i for i,r in enumerate(a) if r[0] == 'R')
    rb = next(i for i,r in enumerate(b) if r[0] == 'R')
    need(a[:ia] == b[:ib] and a[ra+1:] == b[rb+1:], 'shared graph regions')
    text = source.read_text()
    sections = {}
    for name, nxt in [('head','rank64'),('rank64','rank65'),('rank65','suffix'),('suffix','value64')]:
        sections[name] = text.split('\ndef '+name+' ',1)[1].split('\ndef '+nxt+' ',1)[0]
    rowpat = re.compile(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$', re.M)
    expected = {'head': a[:ia], 'rank64': a[ia:ra+1], 'rank65': b[ib:rb+1], 'suffix': a[ra+1:]}
    for name, rows in expected.items():
        got = [[name, op, int(x) if x.isdigit() else x, int(y) if y.isdigit() else y]
               for name,x,op,y in rowpat.findall(sections[name])]
        need(got == rows, name+' literal row mismatch')
    fields = [r[0] for r in a[:ia]]
    struct = text.split('\nstructure Head ',1)[1].split('\ndef head ',1)[0]
    need(re.findall(r'^  (\w+) : R$',struct,re.M) == fields, 'head fields')
    need('  ⟨'+', '.join(fields)+'⟩' in sections['head'], 'head constructor')
    for name in ('head','rank64','rank65','suffix'):
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
    receipt = json.loads((OUT/'result.json').read_bytes())
    need(receipt['status'] == 'PASS' and receipt['exit'] == 0 and receipt['stop_reason'] is None, 'terminal status')
    need(receipt['guards_stable'] and receipt['group_rss_samples'] > 0, 'guard status')
    need(digest(OUT/'compile.log') == receipt['log_sha256'], 'log hash')
    need(digest(OUT/'RationalCarrier64Current.olean') == receipt['object_sha256'] == 'ac3ccf83d8c6c49be8f7b9d306311f2d6fe42f317a4d7fc9b5f875890526b34b', 'object hash')
    need((HERE/'observations/attempt04/result.json').read_bytes() == (OUT/'result.json').read_bytes(), 'receipt snapshot')
    need((HERE/'observations/attempt04/compile.log').read_bytes() == (OUT/'compile.log').read_bytes(), 'log snapshot')
    log = (OUT/'compile.log').read_text()
    need('sorryAx' not in log and 'warning:' not in log and 'error:' not in log, 'compiler diagnostic')
    for name in ('values_equal','zero_iff','value65_eq_expressionAt'):
        need("'DiophantineConsistency.RationalCarrier64Current."+name+"' depends on axioms:" in log, 'axiom report '+name)
    print('PASS exact 28+5+31 / 28+6+31 row binding and checked receipt; no Lean replay')

if __name__ == '__main__':
    main()
