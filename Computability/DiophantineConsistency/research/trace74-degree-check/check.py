#!/usr/bin/env python3
"""Prove exact degree by gate bounds and a fixed-payload modular ray."""
from hashlib import sha256
from pathlib import Path
import gzip, json, sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B')
H=Path(__file__).resolve().parent
D=H.parents[1]
G=D/'research/trace74-mask-coordinate-probe/candidate.json'
C=D/'candidates/ten-positive-qcube-product-square/coefficients'
P=1_000_000_007
def sha(x): return sha256(x).hexdigest()
def need(x,s):
    if not x: raise RuntimeError(s)
graph=G.read_bytes()
need(sha(graph)=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353','graph pin')
d=json.loads(graph)
need(d['witnesses']==['J','F','C','i','T','w','s','n','eta','zeta'],'variable slots')
need(d['fixed_numerals']==['beta','K0','MC','MF'],'port slots')
state={name:(1,1) for name in d['witnesses']}
payloads={}
for port in d['fixed_numerals']:
    entry=d['coefficient_binding']['ports'][port]
    zipped=(C/entry['file']).read_bytes(); raw=gzip.decompress(zipped)
    need(sha(zipped)==entry['parent_gzip_sha256'],'compressed payload '+port)
    need(sha(raw)==entry['raw_sha256'],'raw payload '+port)
    num=int.from_bytes(raw,'little');need(num.bit_length()==entry['bits'],'bit count '+port)
    state[port]=(0,num%P);payloads[port]=sha(raw)
def operand(x):
    return (0,x%P) if type(x) is int else state[x]
need(len(d['source'])==74,'row count')
for name,op,a,b in d['source']:
    need(name not in state and op in ('+','-','*'),'invalid row')
    da,ca=operand(a); db,cb=operand(b)
    if op=='*': state[name]=(da+db,ca*cb%P)
    else:
        top=max(da,db)
        state[name]=(top,((ca if da==top else 0)+(1 if op=='+' else -1)*(cb if db==top else 0))%P)
upper,coefficient=state[d['output']]
need(upper==402 and coefficient!=0,'degree witness')
need(sha(G.read_bytes())==sha(graph),'graph changed')
print(json.dumps({'status':'PASS','graph_sha256':sha(graph),'raw_payload_sha256':payloads,
  'prime':P,'all_variables':'t','beta_mod_prime':state['beta'][1],
  'total_degree_upper':upper,'coefficient_of_t_402_mod_prime':coefficient,
  'conclusion':'exact total degree 402 for the pinned fixed integer ports',
  'scope':'finite external degree check; no positive-zero, halt, iPRA, or file-to-Lean theorem'},sort_keys=True))
