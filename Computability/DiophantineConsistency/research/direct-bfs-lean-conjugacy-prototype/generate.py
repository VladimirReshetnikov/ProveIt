#!/usr/bin/env python3
"""Generate a finite color/row certificate from hash-pinned external inputs."""
from pathlib import Path
import hashlib,json,re,sys
here=Path(__file__).resolve().parent;root=here.parents[1]
files={
 'trans':(root/'con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json','880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'),
 'rows':(root/'research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8'),
 'direct':(root/'research/indexed-tile-enumeration/TILES.json','f06d1b9858281f1adcbc431d3c0df9b07df1a231793629650b2d3c09eac56549')}
for name,(p,h) in files.items():
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise ValueError('pin '+name)
t=json.loads(files['trans'][0].read_text())['transitions']; targets={(q,b):u for q,b,v,d,u in t};order=[0];pi={0:0}
for q in order:
 for b in (0,1):
  u=targets[q,b]
  if u<215 and u not in pi:pi[u]=len(order);order.append(u)
pi[215]=215
if len(pi)!=216 or set(pi.values())!=set(range(216)):raise ValueError('state map')
actions=[[pi[q],b,v,d,pi[u]] for q,b,v,d,u in t]
right={q:6+j for j,q in enumerate(sorted({u for q,b,v,d,u in actions if d==1}))};left={q:205+j for j,q in enumerate(sorted({u for q,b,v,d,u in actions if d==-1}))}
oright={q:6+j for j,q in enumerate(sorted({u for q,b,v,d,u in t if d==1}))};oleft={q:205+j for j,q in enumerate(sorted({u for q,b,v,d,u in t if d==-1}))}
h={i:i for i in range(6)}|{oright[q]:right[pi[q]] for q in oright}|{oleft[q]:left[pi[q]] for q in oleft}
v={0:0,1:1,**{i:i for i in range(434,439)}}|{2*(q+1)+b:2*(pi[q]+1)+b for q in range(216) for b in (0,1)}
if set(h)!=set(range(250)) or set(h.values())!=set(range(250)) or set(v)!=set(range(439)) or set(v.values())!=set(range(439)):raise ValueError('color map')
raw=files['rows'][0].read_text().split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0]
old=[tuple(map(int,re.findall(r'\d+',line))) for line in raw.splitlines()];new=[tuple(x) for x in json.loads(files['direct'][0].read_text())];inv={r:i for i,r in enumerate(new)}
if len(old)!=943 or len(inv)!=943:raise ValueError('rows')
perm=[inv[(h[w],v[n],h[e],v[s])] for w,n,e,s in old]
if sorted(perm)!=list(range(943)) or perm[:2]!=[0,1]:raise ValueError('index map')
def textlist(xs):return ','.join(map(str,xs))
out='''import DirectBFSSymbolicKernel
import DiophantineConsistency.Compact943Data

/-! Finite typed-color conjugacy certificate; no tiling lifting is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSConjugacy

def horizontal : List Nat := ['''+textlist([h[i] for i in range(250)])+''']
def vertical : List Nat := ['''+textlist([v[i] for i in range(439)])+''']
def rowMap : List Nat := ['''+textlist(perm)+''']

def rename (t : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (horizontal.getD t.1 0, vertical.getD t.2.1 0, horizontal.getD t.2.2.1 0, vertical.getD t.2.2.2 0)

theorem horizontal_permutation : horizontal.mergeSort (· ≤ ·) = List.range 250 := by decide
theorem vertical_permutation : vertical.mergeSort (· ≤ ·) = List.range 439 := by decide
theorem row_permutation : rowMap.mergeSort (· ≤ ·) = List.range 943 := by decide
theorem distinguished : rowMap.take 2 = [0,1] := by decide

theorem rows_match : (List.zip Compact943Data.rows rowMap).all
    (fun z => decide (rename z.1 = DirectBFSSymbolicKernel.rows.getD z.2 (0,0,0,0))) = true := by decide

#print axioms DirectBFSConjugacy.horizontal_permutation
#print axioms DirectBFSConjugacy.vertical_permutation
#print axioms DirectBFSConjugacy.row_permutation
#print axioms DirectBFSConjugacy.distinguished
#print axioms DirectBFSConjugacy.rows_match
end DirectBFSConjugacy
'''
p=here/'DirectBFSConjugacy.lean'
if '--check' in sys.argv:
 if p.read_text()!=out:raise ValueError('reproduction')
 print('certificate reproduction passed')
elif p.exists():raise ValueError('refuse overwrite')
else:p.write_text(out)
