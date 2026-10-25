#!/usr/bin/env python3
"""Build a fixed-base radius / binomial Horn-weight arithmetic source.

This is an exact literal source mutation plus inherited certified algebra.
It does not by itself establish the semantic theorem in PROOF.md.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

HERE=Path(__file__).resolve().parent
PACKAGE_ROOT=HERE.parent
DEFAULT_PARENT=PACKAGE_ROOT/'upstream/factorial_free'
DEFAULT_OUTPUT=PACKAGE_ROOT/'stages/fixed_base'

def resolve_parent(parent):
    """Accept either the retained direct component or its complete packet."""
    for candidate in (parent, parent/'direct'):
        if (candidate/'factorial_free_affine/raw_source.json').is_file() and (candidate/'parent/code/terminal_elimination.py').is_file():
            return candidate
    raise ValueError('Expected retained factorial-free direct component, or a packet containing direct/: '+str(parent))

def build(parent, out, support=16, linear_beta=True):
    parent=resolve_parent(parent)
    sys.path.insert(0,str(parent/'parent/code'))
    import terminal_elimination as E
    import factor_horn as F
    import translate_coordinates as T
    old=json.loads((parent/'factorial_free_affine/raw_source.json').read_text())
    new=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    V=F.V
    C=lambda n:{():n} if n else {}
    add=F.add
    scale=lambda p,c:{m:c*a for m,a in p.items() if c*a}
    sq=lambda p:E.multiply(p,p)
    t0=names['t0']; t=add(V(t0),C(16))
    x,y=names['x'],names['y']
    f,r,b=names['crt.growth_majorant_F'],names['mul.1'],names['choose0.output']
    d=names['growth.power_base']; q=names['pow2.output']
    z=names['radix.odd_square_root_half']; sb=names['beta.odd_square_multiplier']
    by=names['self_radix.BH']; a=names['shared.A']
    reps=[add(V(i),C(1)) for i in range(16,25)]
    new['variables'][f]['name']='beta.RB' if linear_beta else 'beta.B_odd_product_squared'
    new['variables'][f]['kind']='gate'
    new['variables'][r]['name']='radius.R'
    new['variables'][r]['kind']='witness'
    new['variables'][z]['name']='radix.progression_parameter'
    new['variables'][sb]['name']='beta.odd_square_multiplier' if linear_beta else 'beta.B_odd_product'
    anchor=add(V(names['add.380']),C(1))
    output=lambda k:V(r) if k==0 else V(names[f'pow{k}.output'])
    requests=[
      (C(16),t,output(0),'index0'),
      (V(b),V(x),output(1),'index12'),
      (V(by),V(x),output(2),'index12'),
      (add(V(q),C(1)),add(V(r),t),output(3),'index2'),
      (V(q),t,output(4),'index0'),
      (add(V(q),C(1)),reps[0],output(5),'index3'),
      (V(q),add(t,C(1)),output(6),None),
      (add(V(q),C(1)),reps[1],output(7),'index5'),
      (add(V(q),C(1)),reps[2],output(8),'index6'),
      (add(V(q),C(1)),reps[3],output(9),'index7'),
      (add(V(q),C(1)),reps[4],output(10),'index8'),
      (V(q),add(V(y),C(1)),output(11),'index9'),
      (add(V(q),C(1)),reps[5],output(12),'index10'),
      (add(V(q),C(1)),reps[6],output(13),'index11'),
      (V(q),V(x),output(14),'index12'),
      (add(V(q),C(1)),reps[7],output(15),'index13'),
      (add(V(q),C(1)),reps[8],output(16),'index14'),
      (add(V(q),C(1)),anchor,output(17),'index15')]
    atoms={tuple(sorted(p.items())):p for nn,kk,mm,_ in requests for p in (nn,kk,mm)}
    frame=add(V(names['shared.W']),C(-2),*[scale(sq(p),-1) for p in atoms.values()])
    H=add(C(2),scale(add(V(r),t),2),*reps)
    removed=[];edits=[];rows=[]
    for i,row in enumerate(old['residuals']):
        p=E.normalize(row['terms']); label=row['label']
        if label=='growth.base_definition':
            removed.append(i);continue
        if i==0:
            if p!={(f,f):-1,(r,):1}:raise ValueError('radius definition differs')
            if linear_beta:
                p=add(V(f),scale(E.multiply(V(r),V(b)),-1));label='beta.RB'
            else:
                p=add(V(f),scale(sq(V(sb)),-1));label='beta.B_odd_product_squared'
        else:
            p=E.substitute(p,f,V(r) if label=='pow0.power_congruence' else V(b))
            p=E.substitute(p,d,C(16))
            if label=='shared.frame_definition':p=frame
            elif label=='self_radix.base_definition':
                p=add(V(by),scale(E.multiply(V(b),H),-1))
                if linear_beta:p=add(p,scale(E.multiply(V(r),V(b)),2),scale(V(f),-2))
            elif label=='radix.odd_square':
                p=add(V(q),scale(V(z),-6),C(-3));label='radix.progression'
            elif label=='bootstrap.beta_base_square_product':
                p=add(V(y),scale(E.multiply(V(f),V(sb) if linear_beta else V(r)),-1));label='bootstrap.beta_base_fixed_radius'
            elif label=='beta.odd_square_multiplier' and not linear_beta:
                p=add(V(sb),scale(E.multiply(V(b),add(scale(V(names['beta.odd_square_root_half']),2),C(1))),-1))
                label='beta.B_odd_product'
        if E.degree(p)>2:raise ValueError((i,'raised degree'))
        newrow={'label':label,'terms':E.as_terms(p)}
        rows.append(newrow)
        if newrow!=row:edits.append({'original_row':i,'old':row,'new':newrow})
    new['residuals']=rows
    new['variant']='fixed_base16_radius_binomial_weights_signed_radix'+('_linear_beta' if linear_beta else '')
    new.pop('metrics',None)
    mutation={
      'schema':'fixed_base_binomial_weights_v1',
      'source_sha256':hashlib.sha256(E.canonical_bytes(old)).hexdigest(),
      'removed_rows':removed,'edits':edits,'added_rows':[],
      'interface':{'t':E.as_terms(t),'x':x,'y':y,'R':r,'B_odd_product_squared':f,'B':b,'q':q,
        'radix_parameter':z,'beta_B_odd_product':sb,
        'BH':by,'H':E.as_terms(H)},
      'requests':[{'base':E.as_terms(nn),'exponent':E.as_terms(kk),'output':E.as_terms(mm),'pair':pair} for nn,kk,mm,pair in requests],
      'linear_beta':linear_beta,
      'semantics':'R=16^t; B=binom(R+t,t); Horn weights 1+jB; '+('y=R B (2v+1)^2' if linear_beta else 'y=R B^2 (2v+1)^2')+'; H=2+2(R+t)+sum(actual representatives); q=6z+3=(BH)^x'}
    if linear_beta:
        mutation['interface'].pop('B_odd_product_squared')
        mutation['interface'].pop('beta_B_odd_product')
        mutation['interface'].update(beta_RB=f,beta_odd_square=sb)
    fac,fc=F.transform(new)
    pr,pc,pm=E.optimize(fac,max_support=support)
    check=E.verify(fac,pr,pc)
    op=json.loads((parent/'parent/data/projected.json').read_text())
    ot=json.loads((parent/'parent/equation/translation_certificate.json').read_text())
    byname={op['variables'][i]['name']:s for i,s in ot['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in byname}
    eq=T.translate(pr,shifts);poly=E.expand(eq)
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for _,m in poly['terms']),
      'monomials':len(poly['terms']),'height':max(abs(c) for c,_ in poly['terms']),
      'row_height':max(abs(c) for rr in eq['residuals'] for c,_ in rr['terms'])}
    out.mkdir(parents=True,exist_ok=True)
    values=[('mutation.json',mutation),('raw_source.json',new),('factored_source.json',fac),('factorization_certificate.json',fc),
      ('projected.json',pr),('projection_certificate.json',pc),('projection_check.json',check),
      ('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),
      ('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metrics)]
    for name,obj in values:(out/name).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent',type=Path,default=DEFAULT_PARENT,help='retained direct component or factorial-free packet (default: ../upstream/factorial_free relative to this script)')
    ap.add_argument('--output',type=Path,default=DEFAULT_OUTPUT,help='write deterministic fixed-base stage (default: ../stages/fixed_base)')
    ap.add_argument('--support',type=int,default=16)
    beta=ap.add_mutually_exclusive_group()
    beta.add_argument('--linear-beta',dest='linear_beta',action='store_true',help='selected y=RB(2v+1)^2 source (default)')
    beta.add_argument('--squared-beta',dest='linear_beta',action='store_false',help='experimental y=RB^2(2v+1)^2 source')
    ap.set_defaults(linear_beta=True)
    args=ap.parse_args();build(args.parent,args.output,args.support,args.linear_beta)
