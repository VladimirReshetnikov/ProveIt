#!/usr/bin/env python3
"""Closed finite proofs replacing H_kappa and symmetry by one helper.

TAUT denotes a Boolean tautology and uses the unchanged rho8/rho6 bridge.
The checker below independently validates every leaf, MP, and closed GEN.
There is no equality rule, substitution rule, or generalization under hypotheses.
"""
from pathlib import Path
import json, hashlib
from dataclasses import dataclass
from functools import cache
from itertools import product
F=('rel',0,0)
I=lambda a,b:('imp',a,b)
Q=lambda i,a:('all',i,a)
N=lambda a:I(a,F)
Ex=lambda i,a:N(Q(i,N(a)))
Eq=lambda a,b:('eq',a,b)
And=lambda a,b:N(I(a,N(b)))
@dataclass(frozen=True,eq=False)
class P:
    rule:str
    form:tuple
    args:tuple=()
@cache
def assumptions(t):
    if t.rule=='HYP':return frozenset((t.form,))
    if t.rule=='MP':return assumptions(t.args[0])|assumptions(t.args[1])
    if t.rule=='GEN':return assumptions(t.args[1])
    return frozenset()
def mp(t,u):
    if t.form[0]!='imp' or t.form[1]!=u.form:raise ValueError('bad MP construction')
    return P('MP',t.form[2],(t,u))
def gen(z,t):
    if assumptions(t):raise ValueError('open GEN construction')
    return P('GEN',Q(z,t.form),(z,t))
def taut(f):return P('TAUT',f)
def prop(f,*premises):
    conditional=f
    for t in reversed(premises):conditional=I(t.form,conditional)
    result=taut(conditional)
    for t in premises:result=mp(result,t)
    return result
def rho1(z,w):return P('rho1',Ex(z,Eq(z,w)))
def rho2(z,a,b):return P('rho2',I(Q(z,I(a,b)),I(Q(z,a),Q(z,b))))
def rho6(z,a):return P('rho6',I(Ex(z,Q(z,a)),a))
def mono(z,t):
    a,b=t.form[1:]
    return mp(rho2(z,a,b),gen(z,t))
def all_imp_ex(z,a,b):
    h=mono(z,taut(I(I(a,b),I(N(b),N(a)))))
    return prop(I(Q(z,I(a,b)),I(Ex(z,a),Ex(z,b))),h,rho2(z,N(b),N(a)))
def export(roots):
    forms=[];fi={};nodes=[];ni={}
    def form(f):
        if f not in fi:fi[f]=len(forms);forms.append(f)
        return fi[f]
    def proof(t):
        if t in ni:return ni[t]
        if t.rule=='MP':args=[proof(x) for x in t.args]
        elif t.rule=='GEN':args=[t.args[0],proof(t.args[1])]
        else:args=list(t.args)
        ni[t]=len(nodes)
        nodes.append({'rule':t.rule,'formula':form(t.form),'args':args})
        return ni[t]
    rootids={name:proof(t) for name,t in roots.items()}
    return {'formulas':forms,'proof_nodes':nodes,'roots':rootids}
def read_export(data):
    def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x
    forms=[freeze(x) for x in data['formulas']];nodes=[]
    for row in data['proof_nodes']:
        r,args=row['rule'],row['args']
        if r=='MP':args=tuple(nodes[x] for x in args)
        elif r=='GEN':args=(freeze(args[0]),nodes[args[1]])
        else:args=tuple(map(freeze,args))
        nodes.append(P(r,forms[row['formula']],args))
    return {name:nodes[i] for name,i in data['roots'].items()}

def serial(z,A):
    witness=Eq(z,z)
    q_to_qimp=mono(z,taut(I(A,I(witness,A))))
    return prop(I(Q(z,A),Ex(z,A)),q_to_qimp,all_imp_ex(z,witness,A),rho1(z,z))

def roots_for(a,b,z):
    e,f=Eq(a,b),Eq(b,a)
    d=And(e,f)
    j=P('J',I(e,Q(z,d)),(a,b,z))
    h=P('H',I(e,Q(z,e)),(a,b,z))
    s=P('SYM',I(e,f),(a,b))
    stable=prop(I(d,Q(z,d)),j)
    box_elim=prop(I(Q(z,d),d),mono(z,stable),serial(z,Q(z,d)),rho6(z,d))
    sym=prop(I(e,f),j,box_elim)
    oldhelper=prop(I(e,Q(z,e)),j,mono(z,taut(I(d,e))))
    qf=prop(I(e,Q(z,f)),h,mono(z,s))
    intro=gen(z,taut(I(e,I(f,d))))
    qand=prop(I(Q(z,e),I(Q(z,f),Q(z,d))),intro,rho2(z,e,I(f,d)),rho2(z,f,d))
    combined=prop(j.form,h,qf,qand)
    return {'symmetry':sym,'ordinary_helper':oldhelper,'combined_from_old_helper_and_symmetry':combined}

def prop_atoms(f):
    if f==F:return set()
    if f[0]=='imp':return prop_atoms(f[1])|prop_atoms(f[2])
    return {f}

def eval_prop(f,v):
    if f==F:return False
    if f[0]=='imp':return not eval_prop(f[1],v) or eval_prop(f[2],v)
    return v[f]

def check(t,seen,counts):
    if t in seen:return
    seen.add(t); counts[t.rule]=counts.get(t.rule,0)+1
    r,f=t.rule,t.form
    if r=='TAUT':
        atoms=sorted(prop_atoms(f),key=repr)
        if any(not eval_prop(f,dict(zip(atoms,bits))) for bits in product((False,True),repeat=len(atoms))):raise ValueError('nontautology')
    elif r=='MP':
        p,q=t.args
        if p.form!=I(q.form,f):raise ValueError('bad MP')
        check(p,seen,counts);check(q,seen,counts)
    elif r=='GEN':
        z,p=t.args
        if assumptions(p) or f!=Q(z,p.form):raise ValueError('open GEN')
        check(p,seen,counts)
    elif r=='rho1':
        z=f[1][1]; atom=f[1][2][1]
        if atom[0]!='eq' or atom[1]!=z or f!=Ex(z,atom):raise ValueError('rho1')
    elif r=='rho2':
        z=f[1][1];a=f[1][2][1];b=f[1][2][2]
        if f!=I(Q(z,I(a,b)),I(Q(z,a),Q(z,b))):raise ValueError('rho2')
    elif r=='rho6':
        a=f[2];z=f[1][1][1]
        if f!=I(Ex(z,Q(z,a)),a):raise ValueError('rho6')
    elif r in ('J','H'):
        a,b,z=t.args;e=Eq(a,b);d=And(e,Eq(b,a)) if r=='J' else e
        if f!=I(e,Q(z,d)):raise ValueError('bad helper')
    elif r=='SYM':
        a,b=t.args
        if f!=I(Eq(a,b),Eq(b,a)):raise ValueError('bad SYM')
    else:raise ValueError('unexpected leaf '+r)

def main():
    allroots={};groups={}
    for a,b,z in [('a','b','k'),(0,0,0),(0,1,2),(1,0,2),(3,3,7),(1,999,1001)]:
        rs=roots_for(a,b,z)
        for name,p in rs.items():
            if assumptions(p):raise ValueError('open root')
            seen=set();counts={};check(p,seen,counts)
            key=f'{a}_{b}_{z}_{name}'
            allroots[key]=p
            groups[key]={'nodes':len(seen),'rules':counts}
    data=export(allroots)
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
    out=Path(__file__).with_name('combined_helper_proofs.json');out.write_bytes(raw)
    reloaded=read_export(json.loads(raw))
    for name,p in reloaded.items():
        if p.form!=allroots[name].form:raise ValueError('reloaded root mismatch')
        check(p,set(),{})
    receipt={'status':'PASS','proof_sha256':hashlib.sha256(raw).hexdigest(),'roots':groups,
             'scope':'Closed syntactic derivations; rho8/rho6-derived classical TAUT leaves. Freshness is required only for standard-equality soundness, not these interderivations. No changed-table theorem.'}
    Path(__file__).with_name('combined_helper_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
