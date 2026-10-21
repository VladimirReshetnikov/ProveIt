#!/usr/bin/env python3
"""Finite schematic proof: one orientation of rho4 recovers its converse.

The native classical propositional basis is inherited from dominated rho8.
The kernel checks K/S, DNE, rho2/rho6, one oriented rho4 family, MP, and
closed-theorem-only GEN.  No variable-renaming or substitution inference.
"""
from pathlib import Path
import hashlib, json
import hilbert as h
assert hashlib.sha256(Path(__file__).with_name('hilbert.py').read_bytes()).hexdigest() == '63396d6ec0b98744b8b4502c316fbdb7fdb018dcda1dbaed0d2e612e5351b7cc'
I,Q,N,NN,Ex,P = h.I,h.Q,h.N,h.NN,h.Ex,h.P
old_ax = h.ax_formula

def allowed(name,args):
    if name == 'DNE':
        x, = args
        return I(NN(x),x)
    if name == 'oriented_rho4':
        a,b,x = args
        assert a == P('a') and b == P('b')
        return I(Q(a,Q(b,x)),Q(b,Q(a,x)))
    return old_ax(name,args)
h.ax_formula = allowed

def trans(p,q):
    x,y=h.form(p)[1:]
    assert h.form(q)[1] == y
    z=h.hyp(x)
    return h.ded(z,h.mp(q,h.mp(p,z)))

def contra(p):
    x,y=h.form(p)[1:]
    ny=h.hyp(N(y));hx=h.hyp(x)
    return h.ded(ny,h.ded(hx,h.mp(ny,h.mp(p,hx))))

def dn(x):
    hx=h.hyp(x)
    return h.ded(hx,h.double(hx))

def unit(i,x):
    # rho6 at neg x: Ex_i Q_i neg x -> neg x.
    # Contraposition, followed by double-negation elimination, is x -> Q_i Ex_i x.
    t=Q(i,Ex(i,x))
    p=trans(dn(x),contra(h.ax('rho6',i,N(x))))
    assert h.form(p) == I(x,NN(t))
    return trans(p,h.ax('DNE',t))

def adjoint_right(i,p):
    # From the closed theorem Ex_i x -> y infer x -> Q_i y.
    xex,y=h.form(p)[1:]
    assert xex[0]=='I' and xex[2]==h.F
    qi=xex[1]
    assert qi[0]=='Q' and qi[1]==i
    nx=qi[2]
    assert nx[0]=='I' and nx[2]==h.F
    x=nx[1]
    return trans(unit(i,x),h.normal(i,p))

def diamond_swap(a,b,y):
    # Ex_b Ex_a y -> Ex_a Ex_b y, obtained by classical duality.
    qa=Q(a,N(y));qb=Q(b,N(y))
    first=contra(h.normal(b,dn(qa)))
    middle=contra(h.ax('oriented_rho4',a,b,N(y)))
    last=contra(h.normal(a,h.ax('DNE',qb)))
    p=trans(trans(first,middle),last)
    assert h.form(p) == I(Ex(b,Ex(a,y)),Ex(a,Ex(b,y)))
    return p

a,b,x=map(P,('a','b','x'))
y=Q(b,Q(a,x))
p=diamond_swap(a,b,y)
p=trans(p,h.existential_mono(a,h.ax('rho6',b,Q(a,x))))
p=trans(p,h.ax('rho6',a,x))
assert h.form(p)==I(Ex(b,Ex(a,y)),x)
p=adjoint_right(b,p)
assert h.form(p)==I(Ex(a,y),Q(b,x))
p=adjoint_right(a,p)
assert h.form(p)==I(Q(b,Q(a,x)),Q(a,Q(b,x)))
outputs={'reversed_commutation':p, 'symmetry_unit':unit(a,x)}
assert h.validate()
assert all(not h.nodes[v]['open'] for v in outputs.values())
used=sorted({n['rule'] for n in h.nodes if n['rule'] not in ('mp','gen','hyp')})
assert used==['DNE','K','S','oriented_rho4','rho2','rho6']
base=Path(__file__).parent
certificate={'nodes':[{**n,'open':sorted(n['open'])} for n in h.nodes],'outputs':outputs}
raw=(json.dumps(certificate,separators=(',',':'))+'\n').encode()
(base/'ordered_commutation_dag.json').write_bytes(raw)
record={'status':'SCHEMATIC_HILBERT_DERIVATION_PASS','nodes':len(h.nodes),'closed_outputs':{k:{'node':v,'formula':h.form(v)} for k,v in outputs.items()},'axioms_used':used,'gen_only_on_closed_theorems':True,'dag_sha256':hashlib.sha256(raw).hexdigest(),'scope':'One oriented rho4 scheme suffices for both directions in the inherited classical calculus. DNE/K/S are supplied by the accepted dominated-rho8 theorem. No global AX parameter restriction, binary table, state reduction, or proof-assistant endpoint is claimed.'}
(base/'ordered_commutation_result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','nodes','axioms_used','dag_sha256']}))
