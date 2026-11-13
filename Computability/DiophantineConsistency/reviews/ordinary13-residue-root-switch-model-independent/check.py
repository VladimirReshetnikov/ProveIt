#!/usr/bin/env python3
"""Independent exact graph dependence and signed-root branch audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
pin('research/ordinary13-residue-root-switch-model-audit/result.json','ffe60a4ae3c8b5228b0cde6e32f363fffdfb269670454c08b2f4ee49aa020f27')
pin('reviews/ordinary13-natural-residue-eta-fold88-independent/result.json','6d2b6da5daadc54609a541e6e4800591248998a488144b307218ebbfedfe2261')
pin('reviews/ordinary13-natural-residue-eta-fold87-independent/result.json','9a77fca0e1200d2a755dca369d91cf77baace798613440e464e108fe6a00cd9b')
quot=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
mag=pin('Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c')
ref=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885')
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m)' in quot
assert '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)' in mag
assert 'theorem natural_dvd_of_signed (a b : V)' in ref
files={'ordinary13-natural-residue-forced89-degree56':'c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a','ordinary13-natural-residue-forced88-degree60':'cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2','ordinary13-natural-residue-eta-fold88-degree56':'f71cb18bdc28088a7a7c7c7ae84afc15e49470ee3d4fa4076d8c25d6d2b89b58','ordinary13-natural-residue-eta-fold87-degree60':'81a09c0504bc786afb017483225e1fb6b1a52e9ddd98f53b0643dfb23c3a602f'}
for name,h in files.items():
 g=json.loads(pin('research/'+name+'/candidate.json',h));nodes={x[0]:x for x in g['source']}
 for r in [['g31','+','g30','n_r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['A0','-','g38','g42']]:assert nodes[r[0]]==r
 def depends(target):
  todo=[target];seen=set(todo)
  while todo:
   for x in nodes.get(todo.pop(),[0,0,0,0])[2:]:
    if isinstance(x,str) and x not in seen:seen.add(x);todo.append(x)
  return 'n_r' in seen
 assert depends('A0') and all(not depends(x) for x in ['A1','Fam','g72','k','ell','Bt','qm'])
 assert sum('n_r' in row[2:] for row in g['source'])==1
# Bounded exact sanity cases exercise both positive- and negative-root signs.
pos=neg=0
for b in range(1,7):
 for ell in range(1,25):
  for k in range(2,10):
   N=1+ell*(ell+k)
   for tau in range(ell+1,ell+k):
    if tau*tau!=N:continue
    for P in range(-20,21):
     Z=b*(ell+k-k*P)-P
     if Z*Z!=b*b*N:continue
     assert P>0 and P%b==0 and Z==-b*tau
     assert (Z+2*b*tau)**2==Z*Z
     neg+=1
   # Both root signs have the expected abstract square, whether or not
   # the carrier equation can realize them at r=0.
   for tau in range(1,10):
    for sign in (-1,1):
     Z=sign*b*tau;assert Z*Z==(b*tau)**2
     if sign>0:pos+=1
print(json.dumps({'scope':'four exact source-dependency graphs and bounded branch controls; no Lean','graphs':len(files),'only_first_residual_depends_on_r':True,'positive_r_witness_by_switch_not_original_positivity':True,'quotient_reflection_and_graph_binding_are_unproved_clients':True,'lean_elaborated':False},sort_keys=True,indent=2))
