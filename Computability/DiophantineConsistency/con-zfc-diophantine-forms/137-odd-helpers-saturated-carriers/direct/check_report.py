#!/usr/bin/env python3
"""Check the exact distinguishing monic restorations printed in section.tex."""
import json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'vendor'))
import terminal_elimination as E
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def v(i,c=1):return {(i,):c}
def sq(p):return E.multiply(p,p)
def need(c,m):
    if not c:raise ValueError(m)
def steps(name):return {r['variable']:r for r in json.loads((HERE/name/'projection_certificate.json').read_text())['steps']}
a,b,c=v(16),v(17),v(18)
aff,qf,last=map(steps,['self_radix','self_radix_qf','self_radix_min'])
expected={55:sq(v(54)),66:add({():93},v(16,30),v(17,32),v(29,14),sq(add({():24},v(16,8),v(17,8),v(29,4)))),69:add({():21},v(17,8),v(18,6),v(35,2),sq(v(67))),74:sq(add({():3},a,v(18,2),v(73,2))),76:sq(v(75)),82:sq(add({():4},v(17,2),v(35,2))),98:sq(add({():7},v(97,2))),106:add({():51},v(18,3),v(102,16),v(104,8),sq(add({():13},c,v(102,4),v(104,2)))),109:sq(add({():9},v(16,2),v(29,2),v(108,2)))}
need(set(qf)-set(aff)==set(expected),'nine additional quadratic-first deletions')
need(set(aff)-set(qf)=={56,67,70,77,83,99,110},'seven wires retained instead')
for i,p in expected.items():need(E.normalize(qf[i]['restoration'])==p,'printed restoration '+str(i))
linear=add({():48},v(16,9),v(17,9),v(29,4),v(34,2),v(37,4),v(42,2),v(46,2),v(49,4),v(53,2),v(58,2),v(63,4),v(64,2),v(72,2),v(79,2),v(112,4),v(113,2))
need(set(last)-set(qf)=={171} and not set(qf)-set(last),'one further affine deletion')
need(E.normalize(last[171]['restoration'])==linear,'printed 17-term affine restoration')
print(json.dumps({'status':'PASS','nine_printed_quadratic_restorations':9,'retained_instead':7,'net_variable_saving':2,'final_affine_restoration_terms':len(linear),'further_variable_saving':1},indent=2,sort_keys=True))
