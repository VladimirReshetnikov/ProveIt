#!/usr/bin/env python3
"""Read-only inspection of package 73's graph and symbolic endpoint source."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
BASE=HERE.parent.parent
PINS={
 'con-zfc-diophantine-forms/73-guard-reanchoring/positive/p13_degree30.json':'e96cd6c8950711a6a26392b27c1ab531cb9df37277e0426cc40cdd1138846a5b',
 'Lean/DiophantineConsistency/Compact44/P73Graph.lean':'37537ef46555cde7a8a1017995988b6ca9ce6a121f07ebe70b0219951758dcac',
 'Lean/DiophantineConsistency/Compact44/P73Halt.lean':'5deb37883e3412c16c1700ced3e35d7674712f259debd15080303f1fadec4ce8',
 'Lean/DiophantineConsistency/Compact44/P73Converse.lean':'37f5609aa42840c5046d58c11566908d641ab557e0ad30e814baf2fb98561289',
 'Lean/DiophantineConsistency/Compact44/P73ConvZero.lean':'7e4cb631e926f6d61fa29756f18458192c384c2904bfa13d869d9a25f93829da',
 'Lean/DiophantineConsistency/Compact44/IPRAPositive73.lean':'b62f982919727f25e5a6e14cb6dfdbe80cb602b8b9b346ce3510d3e006920396',
 'research/thirteen-p73-endpoint/README.md':'336078bdea23b8362972680700178b728dcd17421943985a8eb2c30fc567be45',
}
data={}
for path,digest in PINS.items():
    data[path]=(BASE/path).read_bytes()
    if hashlib.sha256(data[path]).hexdigest()!=digest: raise RuntimeError('hash mismatch '+path)
g=json.loads(data[next(iter(PINS))])
assert g['witnesses']==['j','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
assert g['fixed_numerals']==['beta','K0','MC','MF'] and g['output']=='g91' and len(g['source'])==92
known=set(g['witnesses']+g['fixed_numerals']);deps={};rows=[]
for name,op,a,b in g['source']:
    assert op in ('+','-','*') and name not in known
    assert all(isinstance(x,int) and x>=0 or isinstance(x,str) and x in known for x in (a,b))
    deps[name]=[x for x in (a,b) if isinstance(x,str)]
    rows.append(f'  let {name} := {a} {op} {b}')
    known.add(name)
counts=dict(Counter(row[1] for row in g['source']))
assert counts=={'*':51,'+':24,'-':17}
seen=set();todo=[g['output']]
while todo:
    n=todo.pop()
    if n not in seen:seen.add(n);todo.extend(deps.get(n,[]))
assert len(seen.intersection(deps))==92 and set(g['witnesses']+g['fixed_numerals'])<=seen
lean=data['Lean/DiophantineConsistency/Compact44/P73Graph.lean'].decode()
begin='-- BEGIN LITERAL GRAPH\n';end='  -- END LITERAL GRAPH'
block=lean.split(begin,1)[1].split(end,1)[0].rstrip('\n')
assert block=='\n'.join(rows)
for index,name in enumerate(g['witnesses']):
    assert lean.count(f'  let {name} : Expr (Fin 13) := .var {index}\n')==1
for index,name in enumerate(g['fixed_numerals']):
    assert lean.count(f'  let {name} : Expr (Fin 13) := .constant (p {index})\n')==1
assert lean.split(end,1)[1].startswith('\n  ⟨A0, A1, Aa, As, g91⟩\n')

# Independent full univariate arithmetic: all 13 witnesses scale with t;
# fixed numerals take 5,6,7,8 in F_p. This checks a specialization only.
p=1000003
def trim(a):
    while len(a)>1 and a[-1]%p==0:a.pop()
    return [x%p for x in a]
def add(a,b,s):return trim([(a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return trim(c)
v={n:[0,i+1] for i,n in enumerate(g['witnesses'])};v.update({n:[i+5] for i,n in enumerate(g['fixed_numerals'])})
for n,op,l,r in g['source']:
    a=v[l] if isinstance(l,str) else [l];b=v[r] if isinstance(r,str) else [r]
    v[n]=add(a,b,1) if op=='+' else add(a,b,-1) if op=='-' else mul(a,b)
degree={n:len(v[n])-1 for n in ('A0','A1','As','Aa',g['output'])}
assert degree=={'A0':15,'A1':13,'As':14,'Aa':13,'g91':30} and v['g91'][-1]==6797
endpoint=data['Lean/DiophantineConsistency/Compact44/IPRAPositive73.lean'].decode()
for fragment in ('theorem positiveBridge', 'P73Halt.halts', 'P73Converse.converse',
                 'native_of_positive', 'standard_of_positive', 'reference_of_positive',
                 'CompactSymbolicPortProjections.portsInt (paramKernel rho)'):
    assert fragment in endpoint
print(json.dumps({'status':'PASS','source_hashes':PINS,'gates':92,'operation_counts':counts,
                 'live_gates':len(seen.intersection(deps)),'all_inputs_live':True,
                 'lean_gate_block_matches_json':True,'lean_input_port_output_wiring_matches':True,
                 'ray_prime':p,'ray_degrees':degree,
                 'ray_output_leading_coefficient':v['g91'][-1],
                 'scope':'Source and finite graph evidence only. No Lean replay, general degree proof, full provider ancestry or external payload binding.'},
                indent=2,sort_keys=True))
