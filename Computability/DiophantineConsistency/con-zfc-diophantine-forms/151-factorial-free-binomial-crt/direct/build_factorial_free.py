#!/usr/bin/env python3
"""Explicit factorial-free source: a size majorant replaces factorial authenticity.

This materializes the source proposed in the separate generalized-CRT proof.
Its finite certificates do not replace that semantic proof.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'parent/code'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def put(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(E.canonical_bytes(obj))

def build(out,support=16,square_beta=False,alias_majorant=False,affine_base=False):
    if affine_base and not alias_majorant:raise ValueError('affine base uses the aliased majorant')
    old=json.loads((ROOT/'parent/data/guarded.json').read_text())
    meta=json.loads((ROOT/'parent/data/remainder_transformation.json').read_text())
    n={v['name']:i for i,v in enumerate(old['variables'])}
    t,x,y,Fvar,R,B,U,r,s,bf,q,o,A,Yt=[n[k] for k in ['t0','x','y','fact0.output','mul.1','choose0.output','pow0.output','fact0.remainder','fact0.slack','mul.5','pow2.output','choose0.oslack','shared.A','index0.Y']]
    gr=next(g for g in meta['new_guards'] if g.get('coordinate')==r)
    gs=next(g for g in meta['new_guards'] if g.get('coordinate')==s)
    gq=next(g for g in meta['new_guards'] if g.get('coordinate')==o)
    labels={}
    for i,row in enumerate(old['residuals']):labels.setdefault(row['label'],[]).append(i)
    unique=lambda lab:labels[lab][0] if len(labels[lab])==1 else (_ for _ in ()).throw(ValueError(lab))
    ceiling=unique('fact0.ceiling');rbound=unique('fact0.remainder_bound');yrow=unique('cofinal.beta_base');qrow=unique('choose0.digit_bound');frame=unique('shared.frame_definition')
    bfrows=[i for i,row in enumerate(old['residuals']) if E.normalize(row['terms'])=={(bf,):1,tuple(sorted([Fvar,B])):-1}]
    if len(bfrows)!=1:raise ValueError('BF product definition')
    remove={ceiling,rbound,yrow,bfrows[0],gs['row'],qrow,gq['row']}
    removed_vars={r,s,bf,*gs['auxiliary'],o,*gq['auxiliary']}
    for i,row in enumerate(old['residuals']):
        if i not in remove and i!=gr['row'] and any(removed_vars.intersection(m) for _,m in row['terms']):
            raise ValueError(('nonprivate factorial coordinate',i,row['label']))
    new=copy.deepcopy(old);new['variant']+=':factorial_free_generalized_crt'
    new['variables'][Fvar]['name']='crt.growth_majorant_F'
    new['variables'][U]['name']='growth.power_U'
    d=len(new['variables']);new['variables'].append({'name':'growth.power_base','kind':'gate'})
    z=len(new['variables']);new['variables'].append({'name':'radix.odd_square_root_half','kind':'signed_witness'})
    if square_beta:
        sb=len(new['variables']);new['variables'].append({'name':'beta.odd_square_multiplier','kind':'gate'})
        vb=len(new['variables']);new['variables'].append({'name':'beta.odd_square_root_half','kind':'signed_witness'})
        removed_vars.update(gr['auxiliary'])
    oldbase=F.add(F.V(R),{():1});newbase=F.V(d)
    # The three live gates for pow0 are bound by their literal old polynomials.
    gate_patterns=[({(269,):1,(R,A):-2,(A,):-2},{(269,):1,tuple(sorted([A,d])):-2}),
        ({(270,):1,(R,R):-1,(R,):-2,():-1},{(270,):1,(d,d):-1}),
        ({(272,):1,(R,Yt):-1,(Yt,):-1},{(272,):1,tuple(sorted([d,Yt])):-1})]
    gate_rows={}
    for before,after in gate_patterns:
        before={tuple(sorted(m)):c for m,c in before.items()}
        hits=[i for i,row in enumerate(old['residuals']) if E.normalize(row['terms'])==before]
        if len(hits)!=1:raise ValueError(('pow0 gate shape',before,hits))
        gate_rows[hits[0]]=after
    oldf=E.normalize(old['residuals'][frame]['terms'])
    newf=F.add(oldf,E.multiply(oldbase,oldbase),{(d,d):-1})
    hrow=unique('self_radix.base_definition')
    edits=[];rows=[]
    for i,row in enumerate(old['residuals']):
        if i in remove:continue
        p=E.normalize(row['terms'])
        if i in gate_rows:p=gate_rows[i]
        elif i==frame:p=newf
        elif i==hrow:p=F.add(p,{(B,):-1})
        elif i==gr['row']:
            if square_beta:p={(y,):1,tuple(sorted([Fvar,sb])):-1}
            else:
                a,b,c=gr['auxiliary'];p={(y,):1,(Fvar,):-1,():-3,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
        if alias_majorant:p=E.substitute(p,U,F.V(Fvar))
        rr=dict(row,terms=E.as_terms(p))
        if i==gr['row']:rr['label']='bootstrap.beta_base_square_product' if square_beta else 'bootstrap.beta_base_lower_bound'
        if E.degree(p)>2:raise ValueError('raised residual degree')
        rows.append(rr)
        if rr!=row:edits.append({'original_row':i,'old':row,'new':rr})
    multiplier=2 if alias_majorant else 4
    basepoly={(t,):2,():34} if affine_base else {(t,t):multiplier,(t,):34*multiplier,():289*multiplier}
    rows.append({'label':'growth.base_definition','terms':E.as_terms(F.add(F.V(d),{m:-c for m,c in basepoly.items()}))})
    if not alias_majorant:rows.append({'label':'growth.majorant_definition','terms':E.as_terms({(Fvar,):1,tuple(sorted([t,U])):-2,(U,):-34})})
    rows.append({'label':'radix.odd_square','terms':E.as_terms({(q,):1,(z,z):-4,(z,):-4,():-1})})
    if square_beta:rows.append({'label':'beta.odd_square_multiplier','terms':E.as_terms({(sb,):1,(vb,vb):-4,(vb,):-4,():-1})})
    new['residuals']=rows
    mutation={'schema':'factorial_free_source_v1','source_sha256':hashlib.sha256(E.canonical_bytes(old)).hexdigest(),
        'removed_rows':sorted(remove),'removed_private_variables':sorted(removed_vars),'new_base_variable':d,'new_radix_variable':z,
        'x':x,'reused_guard_auxiliary':[] if square_beta else gr['auxiliary'],'amplifier_constant':2,'square_beta':square_beta,
        'alias_majorant':alias_majorant,'majorant_alias':[[U,Fvar]] if alias_majorant else [],'affine_base':affine_base,
        'new_base_polynomial':E.as_terms(basepoly),
        'added_rows':rows[-((4 if square_beta else 3)-(1 if alias_majorant else 0)):],'edits':edits,
        'interface':{'t0':t,'F':Fvar,'U':U,'R':R,'B':B,'q':q,'y':y,'x':x,
            'radix_square_half':z,'new_power_base':d,'shared_A':A,'pell_t_ordinate':Yt},
        'semantic_change':('F=U=(2(t+1))^t; ' if affine_base else 'F=U=(2(t+1)^2)^t; ' if alias_majorant else 'U=(4(t+1)^2)^t; F=2(t+1)U; ')+('y=F(2v+1)^2' if square_beta else 'y>=F+3')+'; q=(2z+1)^2; H=2+sum(actual representatives); generalized CRT replaces factorial authenticity'}
    if alias_majorant:mutation['interface'].update(U=Fvar,old_U_alias=U)
    if square_beta:mutation['interface'].update(beta_square_multiplier=sb,beta_square_half=vb)
    fac,fc=F.transform(new);pr,pc,_=E.optimize(fac,max_support=support);E.verify(fac,pr,pc)
    op=json.loads((ROOT/'parent/data/projected.json').read_text());ot=json.loads((ROOT/'parent/equation/translation_certificate.json').read_text())
    byname={op['variables'][i]['name']:s for i,s in ot['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in byname}
    eq=T.translate(pr,shifts);poly=E.expand(eq)
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for _,m in poly['terms']),
        'monomials':len(poly['terms']),'height':max(abs(c) for c,_ in poly['terms']),
        'row_height':max(abs(c) for rr in eq['residuals'] for c,_ in rr['terms'])}
    for name,obj in [('mutation.json',mutation),('raw_source.json',new),('factored_source.json',fac),('factorization_certificate.json',fc),
        ('projected.json',pr),('projection_certificate.json',pc),('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),
        ('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metrics)]:put(out/name,obj)
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);p.add_argument('--support',type=int,default=16);p.add_argument('--square-beta',action='store_true');p.add_argument('--alias-majorant',action='store_true');p.add_argument('--affine-base',action='store_true')
    a=p.parse_args();build(a.output or ROOT/('factorial_free_affine' if a.affine_base else 'factorial_free_final' if a.alias_majorant else 'factorial_free_squarebeta' if a.square_beta else 'factorial_free'),a.support,a.square_beta,a.alias_majorant,a.affine_base)
