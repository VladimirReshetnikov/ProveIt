#!/usr/bin/env python3
"""Independent schema-DAG checker; imports no proof-generator code."""
import argparse, hashlib, json
from pathlib import Path
from itertools import product

F=('rel',0,0)
imp=lambda a,b:('imp',a,b)
box=lambda i,a:('all',i,a)
eq=lambda a,b:('eq',a,b)
neg=lambda a:imp(a,F)
ex=lambda i,a:neg(box(i,neg(a)))
kap=lambda a,b:('kap',a,b)
def frozen(v):return tuple(frozen(x) for x in v) if isinstance(v,list) else v
def require(v,message):
    if not v:raise ValueError(message)
def label(v):
    if type(v)is int:return v>=0
    if type(v)is not tuple:return False
    if len(v)==2 and v[0]=='var':return v[1] in ('a','b','c')
    return len(v)==3 and v[0]=='kap' and label(v[1]) and label(v[2])
def valid(f):
    if type(f)is not tuple or not f:return False
    if f[0]in('rel','eq'):return len(f)==3 and all(label(x) for x in f[1:])
    if f[0]=='imp':return len(f)==3 and all(valid(x) for x in f[1:])
    if f[0]=='all':return len(f)==3 and label(f[1]) and valid(f[2])
    return f[0]=='core' and len(f)==4 and all(label(x) for x in f[1:])
def propositional_atoms(f):
    if f==F:return set()
    if f[0]=='imp':return propositional_atoms(f[1])|propositional_atoms(f[2])
    return {f}
def evaluate(f,val):
    if f==F:return False
    return not evaluate(f[1],val) or evaluate(f[2],val) if f[0]=='imp' else val[f]
def verify(data):
    require(data['format']=='uniform-g-schema-v1','format')
    require(data['label_variables']==['a','b','c'] and data['label_functions']=={'kap':2},'label signature')
    fs=list(map(frozen,data['formulas']));ns=data['proof_nodes'];proof_dependencies=[]
    require(all(valid(f) for f in fs),'invalid formula')
    for j,node in enumerate(ns):
        r=node['rule'];args=frozen(node['args']);index=node['formula']
        require(type(index)is int and 0<=index<len(fs),'formula index');f=fs[index];deps=[]
        if r=='MP':
            require(len(args)==2 and all(type(k)is int and 0<=k<j for k in args),'MP earlier nodes')
            require(fs[ns[args[0]]['formula']]==imp(fs[ns[args[1]]['formula']],f),'MP conclusion');deps=list(args)
        elif r=='GEN':
            require(len(args)==2 and label(args[0]) and type(args[1])is int and 0<=args[1]<j,'GEN earlier node')
            require(f==box(args[0],fs[ns[args[1]]['formula']]),'GEN conclusion');deps=[args[1]]
        elif r=='TAUT':
            require(not args,'TAUT args');ats=sorted(propositional_atoms(f),key=repr)
            require(all(evaluate(f,dict(zip(ats,bits))) for bits in product((False,True),repeat=len(ats))),'TAUT validity')
        elif r=='rho1':
            z=f[1][1];atom=f[1][2][1]
            require(not args and atom[0]=='eq' and atom[1]==z and f==ex(z,atom),'rho1 shape')
        elif r=='rho2':
            z=f[1][1];a=f[1][2][1];b=f[1][2][2]
            require(not args and f==imp(box(z,imp(a,b)),imp(box(z,a),box(z,b))),'rho2 shape')
        elif r=='rho6':
            z=f[1][1][1];a=f[2]
            require(not args and f==imp(ex(z,box(z,a)),a),'rho6 shape')
        elif r in ('G','OLD_H','OLD_EUCLID'):
            require(len(args)==(2 if r=='OLD_H' else 3) and all(label(a) for a in args),'axiom label args')
            a,b=args[:2];e=eq(a,b)
            expected=imp(e,box(kap(a,b),e)) if r=='OLD_H' else imp(eq(args[2],a),imp(eq(args[2],b),box(kap(a,b),e) if r=='G' else e))
            require(f==expected,'axiom schema shape')
        else:raise ValueError('unrecognized proof rule '+r)
        proof_dependencies.append(deps)
    a,b,c=[('var',v)for v in ('a','b','c')]
    h=imp(eq(a,b),box(kap(a,b),eq(a,b)));core=('core',a,b,c)
    vr=imp(('rel',a,b),box(c,('rel',a,b)));old=neg(imp(core,imp(vr,neg(h))));new=neg(imp(core,neg(vr)))
    endpoints={
        'reflexivity':eq(a,a),'helper':h,'box_elimination':imp(box(kap(a,b),eq(a,b)),eq(a,b)),
        'euclidean':imp(eq(c,a),imp(eq(c,b),eq(a,b))),
        'G_from_old':imp(eq(c,a),imp(eq(c,b),box(kap(a,b),eq(a,b)))),
        'old_bundle_to_new':imp(old,new),'old_bundle_to_helper':imp(old,h),
        'new_bundle_and_helper_to_old':imp(new,imp(h,old))}
    require(set(data['roots'])==set(endpoints),'root inventory')
    roots={}
    for name,j in data['roots'].items():
        require(type(j)is int and 0<=j<len(ns),'root index')
        require(fs[ns[j]['formula']]==endpoints[name],'root endpoint')
        seen=set();pending=[j]
        while pending:
            k=pending.pop()
            if k in seen:continue
            seen.add(k);pending.extend(proof_dependencies[k])
        rules={ns[k]['rule']for k in seen}
        if name in ('reflexivity','helper','box_elimination','euclidean'):
            require(not rules.intersection({'OLD_H','OLD_EUCLID'}),'circular premise')
        if name=='G_from_old':require('G'not in rules,'circular reverse premise')
        roots[name]={'nodes':len(seen),'rules':sorted(rules)}
    return {'status':'INDEPENDENT_UNIFORM_SCHEMATIC_G_PASS','nodes':len(ns),'formulas':len(fs),'root_count':len(roots),'roots':roots,
        'uniformity':'All label terms are symbolic. A structural substitution induction maps each checked node to a permitted numerical proof node for every a,b,c and every total binary kappa. All proofs are closed; no hypothesis rule is accepted.',
        'scope':'Schematic equality fusion and arbitrary-core bundle transformations. Classical TAUT is supplied by the inherited rho8/rho6 bridge. Not an end-to-end TM proof or proof-assistant kernel check.'}
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('proof',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    raw=a.proof.read_bytes();data=json.loads(raw);r=verify(data);r['sha256']=hashlib.sha256(raw).hexdigest()
    # Verify that even a different proved root cannot replace the requested one.
    bad=json.loads(raw);bad['roots']['helper']=bad['roots']['reflexivity']
    try:verify(bad)
    except ValueError:r['wrong_root_rejected']=True
    else:raise ValueError('wrong endpoint control accepted')
    a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
