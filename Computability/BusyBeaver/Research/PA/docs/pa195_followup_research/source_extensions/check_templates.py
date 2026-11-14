#!/usr/bin/env python3
"""Check explicit finite natural-deduction templates for Gamma relocation.
The proof system is implication + falsity + classical double-negation
elimination.  PA195's unchanged propositional infrastructure implements these
rules by primitive-recursive proof constructors.  This checker does not assert
an exported Lean/PA proof object for that inherited implementation.
"""
from pathlib import Path
import json,argparse
P=Path(__file__).resolve().parent
F=('false',);X=('atom','X');Y=('atom','Y');Z=('atom','Z')
def I(x,y):return ('im',x,y)
def N(x):return I(x,F)
def v(k):return {'rule':'assume','name':k}
def app(f,x):return {'rule':'mp','function':f,'argument':x}
def lam(k,a,p):return {'rule':'deduction','name':k,'formula':a,'body':p}
def exf(p,a):return {'rule':'explosion','proof':p,'formula':a}
def dne(p):return {'rule':'dne','proof':p}
def require(c,m):
 if not c:raise ValueError(m)
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x

def infer(t,ctx):
 r=t['rule']
 if r=='assume':
  require(t['name']in ctx,'undischarged assumption')
  return ctx[t['name']]
 if r=='mp':
  f=infer(t['function'],ctx);x=infer(t['argument'],ctx)
  require(f[0]=='im'and f[1]==x,'modus ponens mismatch')
  return f[2]
 if r=='deduction':
  k=t['name'];a=freeze(t['formula']);require(k not in ctx,'shadowed assumption')
  return I(a,infer(t['body'],dict(ctx,**{k:a})))
 if r=='explosion':
  require(infer(t['proof'],ctx)==F,'explosion lacks falsity')
  return freeze(t['formula'])
 if r=='dne':
  a=infer(t['proof'],ctx)
  require(a[0]=='im'and a[2]==F and a[1][0]=='im'and a[1][2]==F,'DNE shape')
  return a[1][1]
 raise ValueError('unknown rule')

p1=lam('f',N(I(X,Y)),dne(lam('n',N(X),app(v('f'),lam('x',X,exf(app(v('n'),v('x')),Y))))))
p2=lam('f',N(I(X,Y)),lam('y',Y,app(v('f'),lam('x',X,v('y')))))
intro=lam('x',X,lam('n',N(Y),lam('u',I(X,Y),app(v('n'),app(v('u'),v('x'))))))
exchange=lam('f',N(I(X,I(Y,Z))),lam('u',I(Y,I(X,Z)),app(v('f'),lam('x',X,lam('y',Y,app(app(v('u'),v('y')),v('x')))))))
proofs=[
 {'name':'project_first','goal':I(N(I(X,Y)),X),'proof':p1},
 {'name':'project_second_negated','goal':I(N(I(X,Y)),N(Y)),'proof':p2},
 {'name':'combine','goal':I(X,I(N(Y),N(I(X,Y)))),'proof':intro},
 {'name':'exchange_gate_antecedents','goal':I(N(I(X,I(Y,Z))),N(I(Y,I(X,Z)))),'proof':exchange},
]
for p in proofs:require(infer(p['proof'],{})==p['goal'],p['name'])
# A negative control removes the first projection's required classical step.
bad=lam('f',N(I(X,Y)),lam('n',N(X),app(v('f'),lam('x',X,exf(app(v('n'),v('x')),Y)))))
require(infer(bad,{})!=proofs[0]['goal'],'invalid classical projection accepted')
need_same=json.loads((P/'proof_templates.json').read_text());require(need_same==json.loads(json.dumps(proofs)),'template file differs from declared derivations')
# Reread the serialized object and repeat the proof check without Python asserts.
for p in json.loads((P/'proof_templates.json').read_text()):
 require(infer(p['proof'],{})==freeze(p['goal']),p['name']+' serialized')
receipt={'ok':True,'closed_templates':len(proofs),'rules':['assumption','modus ponens','deduction','explosion','double-negation elimination'],'negative_control_rejected':True,'scope':'Finite proof trees over the common classical propositional rules; does not export the inherited numerical proof compiler as a new kernel theorem.'}
ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);args=ap.parse_args()
if args.out:args.out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
