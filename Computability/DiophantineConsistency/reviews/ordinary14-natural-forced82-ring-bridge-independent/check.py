#!/usr/bin/env python3
"""Independently inspect the literal DAG delta and bridge signatures; no Lean."""
from pathlib import Path
import hashlib, json, re
D=Path(__file__).resolve().parents[2]
def pinned(path, digest):
    data=(D/path).read_bytes(); assert hashlib.sha256(data).hexdigest()==digest, path
    return data
paths={
 'g82':('research/ordinary14-root74-natural-forced82/candidate.json','1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'),
 'g86':('research/ordinary14-root74-natural-cancel86/candidate.json','0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170'),
 'l82':('research/ordinary14-natural-forced82-lean-draft/P82NaturalForced.lean','4fd5635afea3327181cdce6d176103195a9d2698f40ab8c40e2ea5c9a9b1fb84'),
 'l86':('research/ordinary14-natural-cancel86-lean-draft/P86NaturalCancel.lean','57015ecd6c66b06867dc05fe392cf02db4a125e646faf9ca16830cb3c0b0b2ef'),
 'ring':('research/ordinary14-natural-forced82-ring-bridge-draft/RingNatural82To86.lean','08e86ba4044b84a32ad7c2e496c61b454fcd4a5ee963b345d8fe75dc420c120e'),
 'model':('research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean','e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854'),
}
d={k:pinned(*v) for k,v in paths.items()}
a,b=json.loads(d['g82']),json.loads(d['g86'])
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
assert len(a['source'])==82 and len(b['source'])==86
assert [a['witnesses'][i] for i in (3,8,11)]==['n_f','n_r','n_y']
def source_rows(data, g):
    text=data.decode(); block=text.split('  -- BEGIN LITERAL GRAPH\n')[1].split('  -- END LITERAL GRAPH\n')[0]
    rows=[]
    for line in block.splitlines():
        parts=line.split(); assert len(parts)==6 and parts[0]=='let' and parts[2]==':='
        def atom(t): return int(t) if t.isdecimal() else t
        rows.append([parts[1],parts[4],atom(parts[3]),atom(parts[5])])
    assert rows==g['source']
    for i,name in enumerate(g['witnesses']): assert f'  let {name} : Expr (Fin 14) := .var {i}\n' in text
    for i,name in enumerate(g['fixed_numerals']): assert f'  let {name} : Expr (Fin 14) := .constant (p {i})\n' in text
    assert '  ⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in text
source_rows(d['l82'],a); source_rows(d['l86'],b)
x={row[0]:row[1:] for row in a['source']}; y={row[0]:row[1:] for row in b['source']}
assert len(x)==82 and len(y)==86
for n in ('f','r','y'): assert y[n]==['+',f'n_{n}',1] and n not in x
assert y['zeta']==['+','n_zeta',1] and y['k']==['+','eta','zeta']
assert y['g52']==['-','k','R'] and y['r0']==['-','g52',1]
assert x['kbase']==['+','eta','n_zeta'] and x['k']==['+','kbase',1]
assert x['r0']==['-','kbase','R']
# On translating the 86 input by -1, the three deleted source nodes are
# exactly the corresponding unshifted 82 inputs. The displayed k/r0 cuts
# are ring identities. Verify all remaining nodes by structural congruence.
ren={'f':'n_f','r':'n_r','y':'n_y'}
assert set(y)-set(x)==set(ren)|{'zeta','g52'}
assert set(x)-set(y)=={'kbase'}
shared=set(x)&set(y)-{'k','r0'}
for name in shared:
    op,left,right=y[name]
    assert x[name]==[op,ren.get(left,left),ren.get(right,right)], name
ring=d['ring'].decode(); model=d['model'].decode()
assert 'fun j => if j = 3 ∨ j = 8 ∨ j = 11 then v j - 1 else v j' in ring
assert '(P82NaturalForced.graph p).output.evalRing v =\n      (P86NaturalCancel.graph p).output.evalRing (down v)' in ring
assert 'v82 3 = v86 3 + 1 ∧ v82 8 = v86 8 + 1 ∧ v82 11 = v86 11 + 1' in model
assert '∀ j, j ≠ 3 → j ≠ 8 → j ≠ 11 → v82 j = v86 j' in model
assert '∃ f r y : V, v 3 = f + 1 ∧ v 8 = r + 1 ∧ v 11 = y + 1' in model
assert '(predecessors : ∀ v, InternalZero (P82NaturalForced.graph p).output v →\n      HasThreePredecessors v)' in model
assert '(∃ v, InternalZero (P82NaturalForced.graph p).output v) ↔\n      ∃ w, InternalZero (P86NaturalCancel.graph p).output w' in model
assert '(internalZero_iff_of_related p hw).mp hv' in model
assert '(internalZero_iff_of_related p (related_lift w)).mpr hw' in model
print(json.dumps({'scope':'pinned literal graph delta and source signature inspection; no Lean elaboration or model theorem',
  'shared_structural_rows_checked':len(shared), 'translated_slots':[3,8,11],
  'explicit_successor_assumption_checked':True,'lean_graph_sources_compared_to_json':2},sort_keys=True,indent=2))
