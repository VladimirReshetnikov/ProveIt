#!/usr/bin/env python3
"""Schematic closed-proof certificate for G fusion, independent of the K core.

Adapted from the G223 package's merged_euclidean_helper_certificate.py and
combined_helper_certificate.py. Original finite-instance construction is
credited to that package. This version keeps labels as formal terms and
checks the proof before any natural-number substitution; kappa is arbitrary.

Python standard library only. Run with --output DIR. This is an executable
mathematical proof certificate, not a Lean/Rocq kernel theorem.
"""
from pathlib import Path
from dataclasses import dataclass
from functools import cache
from itertools import product
import argparse, hashlib, json

F = ('rel', 0, 0)
I = lambda a,b: ('imp',a,b)
Q = lambda z,a: ('all',z,a)
E = lambda a,b: ('eq',a,b)
N = lambda a: I(a,F)
Ex = lambda z,a: N(Q(z,N(a)))
And = lambda a,b: N(I(a,N(b)))
kap = lambda a,b: ('kap',a,b)
A,B,C = [('var',x) for x in ('a','b','c')]

@dataclass(frozen=True,eq=False)
class Proof:
    rule: str
    form: tuple
    args: tuple = ()

def mp(t,u):
    if t.form[0]!='imp' or t.form[1]!=u.form: raise ValueError('MP construction')
    return Proof('MP',t.form[2],(t,u))
def gen(z,t): return Proof('GEN',Q(z,t.form),(z,t))
def taut(f): return Proof('TAUT',f)
def prop(f,*premises):
    result=f
    for p in reversed(premises): result=I(p.form,result)
    out=taut(result)
    for p in premises: out=mp(out,p)
    return out
def rho1(z,w): return Proof('rho1',Ex(z,E(z,w)))
def rho2(z,a,b): return Proof('rho2',I(Q(z,I(a,b)),I(Q(z,a),Q(z,b))))
def rho6(z,a): return Proof('rho6',I(Ex(z,Q(z,a)),a))
def mono(z,t):
    a,b=t.form[1:]
    return mp(rho2(z,a,b),gen(z,t))
def contra(t):
    a,b=t.form[1:]
    return prop(I(N(b),N(a)),t)
def emono(z,t): return contra(mono(z,contra(t)))
def all_imp_ex(z,a,b):
    h=mono(z,taut(I(I(a,b),I(N(b),N(a)))))
    return prop(I(Q(z,I(a,b)),I(Ex(z,a),Ex(z,b))),h,rho2(z,N(b),N(a)))
def serial(z,a):
    witness=E(z,z)
    h=mono(z,taut(I(a,I(witness,a))))
    return prop(I(Q(z,a),Ex(z,a)),h,all_imp_ex(z,witness,a),rho1(z,z))
@cache
def merged(a,b,c):
    return Proof('G',I(E(c,a),I(E(c,b),Q(kap(a,b),E(a,b)))),(a,b,c))
@cache
def reflexivity(x):
    e=E(x,x); z=kap(x,x); d=E(z,x)
    h=prop(I(d,Q(z,e)),merged(x,x,z))
    return mp(rho6(z,e),mp(emono(z,h),rho1(z,x)))
@cache
def helper(a,b):
    return prop(I(E(a,b),Q(kap(a,b),E(a,b))),merged(a,b,a),reflexivity(a))
@cache
def box_elim(a,b):
    e=E(a,b); z=kap(a,b)
    double=prop(I(Q(z,Q(z,e)),e),serial(z,Q(z,e)),rho6(z,e))
    return prop(I(Q(z,e),e),mono(z,helper(a,b)),double)
@cache
def euclid(a,b,c):
    return prop(I(E(c,a),I(E(c,b),E(a,b))),merged(a,b,c),box_elim(a,b))
def reverse(a,b,c):
    old_h=Proof('OLD_H',I(E(a,b),Q(kap(a,b),E(a,b))),(a,b))
    old_e=Proof('OLD_EUCLID',I(E(c,a),I(E(c,b),E(a,b))),(a,b,c))
    return prop(merged(a,b,c).form,old_e,old_h)
def export(roots):
    forms=[]; fi={}; nodes=[]; ni={}
    def form(f):
        if f not in fi: fi[f]=len(forms); forms.append(f)
        return fi[f]
    def visit(t):
        if t in ni:return ni[t]
        if t.rule=='MP':args=[visit(u) for u in t.args]
        elif t.rule=='GEN':args=[t.args[0],visit(t.args[1])]
        else:args=list(t.args)
        ni[t]=len(nodes);nodes.append(dict(rule=t.rule,formula=form(t.form),args=args))
        return ni[t]
    ids={k:visit(t) for k,t in roots.items()}
    return dict(format='uniform-g-schema-v1',label_variables=['a','b','c'],
                label_functions={'kap':2},formulas=forms,proof_nodes=nodes,roots=ids)
def make():
    core=('core',A,B,C)
    vr=I(('rel',A,B),Q(C,('rel',A,B)))
    h=helper(A,B).form
    old=N(I(core,I(vr,N(h))))
    new=And(core,vr)
    return export(dict(
        reflexivity=reflexivity(A),helper=helper(A,B),box_elimination=box_elim(A,B),
        euclidean=euclid(A,B,C),G_from_old=reverse(A,B,C),
        old_bundle_to_new=taut(I(old,new)),old_bundle_to_helper=taut(I(old,h)),
        new_bundle_and_helper_to_old=taut(I(new,I(h,old)))))

def freeze(v):return tuple(map(freeze,v)) if isinstance(v,list) else v
def need(p,m):
    if not p:raise ValueError(m)
def label(t):
    if type(t) is int:return t>=0
    if not isinstance(t,tuple):return False
    if len(t)==2 and t[0]=='var':return t[1] in ('a','b','c')
    return len(t)==3 and t[0]=='kap' and label(t[1]) and label(t[2])
def formula(t):
    if not isinstance(t,tuple) or not t:return False
    tag=t[0]
    if tag in ('eq','rel'):return len(t)==3 and label(t[1]) and label(t[2])
    if tag=='imp':return len(t)==3 and formula(t[1]) and formula(t[2])
    if tag=='all':return len(t)==3 and label(t[1]) and formula(t[2])
    return tag=='core' and len(t)==4 and all(label(x) for x in t[1:])
def atoms(f):
    if f==F:return set()
    if f[0]=='imp':return atoms(f[1])|atoms(f[2])
    return {f}
def truth(f,v):
    if f==F:return False
    if f[0]=='imp':return not truth(f[1],v) or truth(f[2],v)
    return v[f]
def check(data):
    need(data['format']=='uniform-g-schema-v1','schema format')
    forms=list(map(freeze,data['formulas']));nodes=data['proof_nodes'];deps=[];counts={}
    need(all(formula(f) for f in forms),'malformed schematic formula')
    for j,node in enumerate(nodes):
        r=node['rule'];idx=node['formula'];a=freeze(node['args'])
        need(type(idx)is int and 0<=idx<len(forms),'formula index');f=forms[idx]
        counts[r]=counts.get(r,0)+1;uses=[]
        if r=='MP':
            need(len(a)==2 and all(type(x)is int and 0<=x<j for x in a),'MP order')
            need(forms[nodes[a[0]]['formula']]==I(forms[nodes[a[1]]['formula']],f),'MP formula');uses=list(a)
        elif r=='GEN':
            z,p=a;need(label(z) and type(p)is int and 0<=p<j,'GEN args')
            need(f==Q(z,forms[nodes[p]['formula']]),'GEN formula');uses=[p]
        elif r=='TAUT':
            aa=sorted(atoms(f),key=repr)
            need(all(truth(f,dict(zip(aa,v))) for v in product((False,True),repeat=len(aa))),'non-tautology')
        elif r=='rho1':
            z=f[1][1];e=f[1][2][1]
            need(e[0]=='eq' and e[1]==z and f==Ex(z,e),'rho1')
        elif r=='rho2':
            z=f[1][1];x,y=f[1][2][1:]
            need(f==I(Q(z,I(x,y)),I(Q(z,x),Q(z,y))),'rho2')
        elif r=='rho6':
            z=f[1][1][1];x=f[2]
            need(f==I(Ex(z,Q(z,x)),x),'rho6')
        elif r in ('G','OLD_H','OLD_EUCLID'):
            need(all(label(x) for x in a),'schema labels');x,y=a[:2];e=E(x,y)
            if r=='G':expected=I(E(a[2],x),I(E(a[2],y),Q(kap(x,y),e)))
            elif r=='OLD_H':expected=I(e,Q(kap(x,y),e))
            else:expected=I(E(a[2],x),I(E(a[2],y),e))
            need(f==expected,r)
        else:raise ValueError('Forbidden rule '+r)
        deps.append(uses)
    core=('core',A,B,C);vr=I(('rel',A,B),Q(C,('rel',A,B)))
    hh=I(E(A,B),Q(kap(A,B),E(A,B)));old=N(I(core,I(vr,N(hh))));new=And(core,vr)
    expected_roots={
        'reflexivity':E(A,A), 'helper':hh,
        'box_elimination':I(Q(kap(A,B),E(A,B)),E(A,B)),
        'euclidean':I(E(C,A),I(E(C,B),E(A,B))),
        'G_from_old':I(E(C,A),I(E(C,B),Q(kap(A,B),E(A,B)))),
        'old_bundle_to_new':I(old,new), 'old_bundle_to_helper':I(old,hh),
        'new_bundle_and_helper_to_old':I(new,I(hh,old))}
    need(set(data['roots'])==set(expected_roots),'root inventory')
    roots={}
    for name,j in data['roots'].items():
        need(type(j)is int and 0<=j<len(nodes),'root index');seen=set();todo=[j]
        for i in todo:
            if i in seen:continue
            seen.add(i);todo.extend(deps[i])
        need(forms[nodes[j]['formula']]==expected_roots[name],'wrong root endpoint')
        rules={nodes[i]['rule'] for i in seen}
        if name in ('reflexivity','helper','box_elimination','euclidean'):
            need(not rules & {'OLD_H','OLD_EUCLID'},'circular old premise')
        if name=='G_from_old':need('G' not in rules,'circular G premise')
        roots[name]=dict(nodes=len(seen),rules=sorted(rules))
    return dict(status='UNIFORM_SCHEMATIC_G_PROOF_PASS',nodes=len(nodes),formulas=len(forms),
                root_count=len(roots),rules=counts,roots=roots,
                scope='Formal label terms, arbitrary binary kappa, arbitrary core. Every natural-label substitution preserves the checked proof. TAUT uses the inherited rho8/rho6 propositional bridge. No equality freshness, set-theory axiom, open hypothesis, or proof-assistant kernel is assumed.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    a.output.mkdir(parents=True,exist_ok=True)
    data=make();raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
    path=a.output/'uniform_g_proof.json';path.write_bytes(raw)
    result=check(json.loads(path.read_text()));result['sha256']=hashlib.sha256(raw).hexdigest()
    # Semantic negative controls: circular old premise and a corrupt G binder.
    bad=json.loads(raw);j=bad['roots']['helper'];bad['proof_nodes'][j]['rule']='OLD_H'
    bad['proof_nodes'][j]['args']=[A,B]
    try:check(bad)
    except ValueError:result['old_helper_root_rejected']=True
    else:raise ValueError('circular negative control accepted')
    bad=json.loads(raw)
    target=next(n for n in bad['proof_nodes'] if n['rule']=='G')
    target['args'][0]=0
    try:check(bad)
    except ValueError:result['changed_G_instance_rejected']=True
    else:raise ValueError('G negative control accepted')
    (a.output/'uniform_g_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
