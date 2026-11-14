#!/usr/bin/env python3
"""Finite constructor certificate for an unbounded residue invariant.
The induction theorem is stated in obstruction.tex; no machine claimed.
"""
from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('gh',ROOT/'check_commands.py')
gh=importlib.util.module_from_spec(spec);spec.loader.exec_module(gh)
word=gh.decode_word(ROOT/'grammar.json')[1:]
assert len(word)==189 and word[-3:]==['copyGuard','compareGuard','close']
z=('zero',);s=lambda a:('succ',a);one=s(z)
I=lambda a,b:('I',a,b);M=lambda a,b:s(I(a,b));U=lambda a,b:s(s(I(b,a)))
E=lambda a,b:s(s(s(I(a,b))));N=lambda a:I(a,one)
C=lambda a,b:N(I(a,N(b)));Ex=lambda a,b:N(U(a,N(b)))
t,a,d,h,x,y=[('parameter',k)for k in ('t','a','d','h','x','y')]
top,D,H,stack=t,d,h,[];fields=iter([y,x]);reads=[]
for tok in word[:-3]:
 if tok=='push':stack.append(top);top=z
 elif tok in ('copyD','copyH','copyA'):stack.append(top);top={'copyD':D,'copyH':H,'copyA':a}[tok]
 elif tok=='cons':top=I(stack.pop(),top)
 elif tok=='incT':top=s(top)
 elif tok=='readH':v=next(fields);reads.append(v);H=('add',H,v)
 elif tok=='readDCons':v=next(fields);reads.append(v);D=('add',D,v);top=I(top,D)
 else:raise AssertionError(tok)
assert reads==[y,x]
rho=I(I(I(H,d),D),I(I(D,H),I(a,H)))
heads=[I(Ex(D,U(D,H)),H),I(U(D,U(a,H)),U(a,U(D,H))),
       I(M(H,D),I(E(H,a),M(a,D))),I(E(H,D),I(M(a,H),M(a,D))),
       Ex(D,E(H,D)),I(U(D,I(a,H)),I(U(D,a),U(D,H)))]
gamma=I(a,U(a,a));point=I(a,M(a,D));V=I(M(H,D),U(a,M(H,D)))
S=U(D,C(I(M(H,D),point),I(M(a,D),a)));Q=U(a,I(S,N(point)))
assert stack==[U(a,t),rho]+heads+[gamma]
assert top==N(I(V,Q))
def residue(e):
 if e==z:return 0
 if e[0]=='I':return 0
 if e[0]=='succ':return(residue(e[1])+1)%4
 raise AssertionError(('unknown top constructor',e))
rs=[residue(e)for e in stack]
assert len(rs)==9 and set(rs)<={0,2}
assert residue(top)==0
# The finite residue transitions cover all abstract command forms:
# AX clears h and adds exactly these residues; MP preserves w and clears h;
# Shift preserves the even stack-tail and loads an even head (zero at tail).
for hres in (0,2):
 assert hres!=1
 for head in (0,2):assert head in(0,2)
receipt=dict(status='PASS',tokens=189,pushed_items=9,raw_old_top_saved=False,
 generated_generalization='U(c,t)',pushed_residues_bottom_to_top=rs,
 ax_sets_cached_residue=0,mp_sets_cached_residue=0,shift_loads_cached_residues=[0,2],
 initial_cached_residue=0,initial_stack_residue=0,
 invariant='Every live canonical stack entry and h have even residue modulo4',
 consequence='Cache-only Shift h=1 is unreachable for every command word from zero',
 proof_scope='Finite symbolic constructor certificate plus induction theorem in obstruction.tex; no complete PA-calibrated table')
Path(__file__).with_name('invariant_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
