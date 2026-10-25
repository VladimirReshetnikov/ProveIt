#!/usr/bin/env python3
"""Exact delta and polynomial audit, importing no producer or eliminator.

The inherited independently implemented algebra checker supplies the already
reviewed Horn factorization and monic projection replay. This file constructs
the new source delta afresh. It does not test or decide consistency.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'inherited_common/code'))
import inherited_independent_algebra as I

def get(p):return json.loads(p.read_text())
def pins():
    # Exact inherited inputs are also named in the source ledger.
    return get(HERE/'SOURCE_PINS.json')

def check_delta(d):
    old=d['parent'];meta=d['metadata']; rc=d['remainder_metadata']; c=d['delta_certificate']
    for key,obj in [('guarded.json',old),('parent_transform_certificate.json',meta),('remainder_transformation.json',rc)]:
        I.need(I.sha(obj)==pins()[key],'pinned inherited input '+key)
    I.need(I.sha(old)==c['input_sha256'] and I.sha(d['source'])==c['output_sha256'],'source hash binding')
    source=copy.deepcopy(old); names={v['name']:i for i,v in enumerate(source['variables'])}
    q=names['pow2.output'];o=names['choose0.oslack']
    gs=[g for g in rc['new_guards'] if g['kind']=='front_nonnegative' and g['coordinate']==o]
    I.need(len(gs)==1,'old output guard census');g=gs[0];ri=g['row'];a,b,z0=g['auxiliary']
    expected=I.add(I.v(o),{(a,a):-1,(b,b):-1,(z0,z0):-1,(z0,):-1})
    I.need(I.norm(source['residuals'][ri])==expected,'old output sign guard')
    I.need(not any(j!=ri and any(v in m for m in I.norm(row) for v in [a,b,z0]) for j,row in enumerate(source['residuals'])),'output guard not private')
    removed=source['residuals'].pop(ri)
    z=len(source['variables']); source['variables'].append({'name':'odd_radix.root','kind':'signed_witness'})
    scale=c.get('radix_scale',1);I.need(scale in [1,3],'unproved radix scale')
    row={'label':'odd_radix.square','terms':I.terms(I.add(I.v(q),{(z,z):-4*scale*scale,(z,):-4*scale*scale,():-scale*scale}))}
    source['residuals'].append(row);source['variant']+=(':odd_square_radix' if scale==1 else ':odd_square_multiple_three_radix');source.pop('metrics',None)
    I.need(c['removed_row_index']==ri and c['removed_row']==removed,'output guard deleted incorrectly')
    I.need(c['removed_private_auxiliaries']==[a,b,z0] and c['added_variable']==z and c['added_row']==row,'square witness delta')
    I.need(c['radix_coordinate']==q and c['output_slack_coordinate']==o,'square named coordinates')
    if 'center_changes' in c:
        I.need(c['parent_metadata_sha256']==I.sha(meta),'center metadata hash')
        A=names['shared.A'];H=names['cap.H'];f=names['cap.f'];R=names['cap.R'];C=meta['cap_variables']['Y'];hq=names['cap.h']
        replacements={
          'cap.comparison_constructor':('cap.deterministic_factor',I.add(I.v(f),I.sc(I.v(H),-1),I.mul(I.v(A),I.v(H)))),
          'cap.index_residue':('cap.index_residue',I.add(I.v(R),I.sc(I.norm(meta['anchor_index']),-1),I.sc(I.mul(I.v(C),I.v(hq)),-1)))
        }
        linear=c['linear_full_orientation']
        if linear:
            p={}
            I.need(len(meta['seed_data'])==14,'canonical orientation census')
            for seed in meta['seed_data']:
                X,Y=seed['pair'];dif=I.add(I.v(Y),I.sc(I.norm(seed['exponent']),-1))
                p=I.add(p,I.mul(dif,dif),I.con(1),I.sc(I.v(X),-1))
            p=I.add(p,I.sc(I.mul(I.add(I.v(A),I.con(-1)),I.v(meta['pooled_quotient'])),-1))
            replacements['cap.pooled_index_residue']=('cap.pooled_index_residue',p)
        changes=[]
        for i,r in enumerate(source['residuals']):
            if r['label'] in replacements:
                lab,p=replacements[r['label']];nr={'label':lab,'terms':I.terms(p)}
                changes.append({'row':i,'before':r,'after':nr});source['residuals'][i]=nr
        I.need(changes==c['center_changes'],'center exact source edits')
        I.need(c['center_unused_coordinate']==names['cap.d'],'center deleted coordinate name')
        I.need(not any(names['cap.d'] in m for r in source['residuals'] for m in I.norm(r)),'center d escaped')
        source['variant']+=':deterministic_center_modC'+(':linear14' if linear else ':squared14')
    if 'ceiling_deleted_guards' in c:
        F=names['fact0.output'];r=names['fact0.remainder'];s=names['fact0.slack'];V0=names['pow0.output']
        front=[g for g in rc['new_guards'] if g['kind']=='front_nonnegative' and g['coordinate'] in [r,s]]
        I.need(len(front)==2,'ceiling front guard census')
        labels=set();deletions=[]
        for g in front:
            a,b,cc=g['auxiliary'];coord=g['coordinate'];rr=old['residuals'][g['row']]
            I.need(I.norm(rr)==I.add(I.v(coord),{(a,a):-1,(b,b):-1,(cc,cc):-1,(cc,):-1}),'ceiling sign formula')
            I.need(not any(another['label']!=rr['label'] and any(v in m for m in I.norm(another) for v in [a,b,cc]) for another in source['residuals']),'ceiling guard auxiliaries escape')
            labels.add(rr['label']);deletions.append({'row':rr,'coordinate':coord,'private':g['auxiliary']})
        I.need(deletions==c['ceiling_deleted_guards'],'ceiling deleted row delta')
        source['residuals']=[rr for rr in source['residuals'] if rr['label'] not in labels]
        if 'ceiling_product_variable' in c:
            u=len(source['variables']);a=u+1;b=u+2;cc=u+3
            I.need(u==c['ceiling_product_variable'] and [a,b,cc]==c['ceiling_guard_auxiliaries'],'ceiling fresh variables')
            source['variables'] += [{'name':'ceiling_product.u','kind':'gate'}]+[{'name':'ceiling_product.'+v,'kind':'integer_guard'} for v in ('a','b','c')]
            pr={'label':'ceiling_product.u','terms':I.terms(I.add(I.v(u),I.sc(I.mul(I.v(F),I.v(s)),-1)))}
            rem=I.add(I.v(V0),I.v(s),I.sc(I.v(F),-1),I.sc(I.v(u),-1))
            gr={'label':'ceiling_product.strict_guard','terms':I.terms(I.add(I.mul(I.v(u),rem),{():-1,(a,a):-1,(b,b):-1,(cc,cc):-1,(cc,):-1}))}
            I.need([pr,gr]==c['ceiling_added_rows'],'ceiling exact product guard')
            source['residuals'] += [pr,gr];source['variant']+=':strict_ceiling_product'
            B=names['choose0.output']; prod=I.mul(I.v(u),rem)
            prod=I.sub(prod,u,I.mul(I.v(F),I.v(s)))
            prod=I.sub(prod,V0,I.add(I.mul(I.v(F),I.v(B)),I.sc(I.v(s),-1)))
            target=I.mul(I.mul(I.v(F),I.v(F)),I.mul(I.add(I.v(B),I.sc(I.v(s),-1),I.con(-1)),I.v(s)))
            I.need(prod==target,'ceiling strict-product identity')
        else:
            I.need(scale==3,'simple interval product requires the nonunit radix')
            a=len(source['variables']);b=a+1;cc=a+2
            I.need([a,b,cc]==c['ceiling_guard_auxiliaries'],'simple ceiling fresh variables')
            source['variables'] += [{'name':'ceiling_product.'+v,'kind':'integer_guard'} for v in ('a','b','c')]
            strict=c.get('ceiling_strict',True)
            label='ceiling_product.strict_guard' if strict else 'ceiling_product.weak_guard'
            gr={'label':label,'terms':I.terms(I.add(I.mul(I.v(r),I.v(s)),{():-int(strict),(a,a):-1,(b,b):-1,(cc,cc):-1,(cc,):-1}))}
            I.need([gr]==c['ceiling_added_rows'],'simple strict ceiling product')
            source['residuals'].append(gr);source['variant']+=(':strict_ceiling_interval_product' if strict else ':weak_ceiling_interval_product')
    I.need(source==d['source'],'complete new source mismatch')

def load(endpoint):
    d={n:get(endpoint/(n+'.json')) for n in ['source','delta_certificate','factored_source','factorization_certificate','projected','projection_certificate','translation_certificate','equation','expanded_polynomial','METRICS']}
    base=HERE/'inherited_common/data'
    d.update(parent=get(base/'guarded.json'),metadata=get(base/'parent_transform_certificate.json'),remainder_metadata=get(base/'remainder_transformation.json'))
    return d

def check(d):
    check_delta(d)
    f=I.factorization(d['source'],d['factored_source'],d['factorization_certificate'])
    p=I.projection(d['factored_source'],d['projected'],d['projection_certificate'])
    t=I.translation(d['projected'],d['equation'],d['translation_certificate'])
    poly,used=I.literal(d['equation'])
    I.need(poly==I.norm(d['expanded_polynomial']),'SOS coefficients differ')
    I.need(used==set(range(len(d['equation']['variables']))),'unused final coordinate')
    met={'variables':len(d['equation']['variables']),'rows':len(d['equation']['residuals']),
         'degree':I.deg(poly),'monomials':len(poly),'height':max(map(abs,poly.values())),
         'row_height':max(abs(c) for row in d['equation']['residuals'] for c,m in row['terms'])}
    I.need(met==d['METRICS'],'metrics mismatch')
    return met|{'factorization_edits':f,'monic_projection_steps':p,'integral_translations':t,
                'equation_sha256':I.sha(d['equation']),'polynomial_sha256':I.sha(d['expanded_polynomial'])}

def controls(d):
    tests=[]
    def trial(name,fn):
        z=copy.deepcopy(d);fn(z)
        try:check(z)
        except (ValueError,KeyError,IndexError,TypeError) as exc:tests.append({'name':name,'rejected':True,'reason':str(exc)})
        else:raise ValueError('Corruption not rejected: '+name)
    trial('wrong_odd_square_constant',lambda z:z['delta_certificate']['added_row']['terms'][0].__setitem__(0,-2))
    if 'center_changes' in d['delta_certificate']:
        trial('missing_center_edit',lambda z:z['delta_certificate']['center_changes'].pop())
    if 'ceiling_added_rows' in d['delta_certificate']:
        trial('changed_ceiling_guard',lambda z:z['delta_certificate']['ceiling_added_rows'][-1]['terms'][0].__setitem__(0,0))
    trial('wrong_monic_restoration',lambda z:z['projection_certificate']['steps'][0]['restoration'][0].__setitem__(0,1234))
    trial('wrong_translation',lambda z:z['translation_certificate']['shifts'][0].__setitem__(1,77))
    trial('wrong_collected_coefficient',lambda z:z['expanded_polynomial']['terms'][0].__setitem__(0,1234))
    return tests

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--endpoint',type=Path,default=HERE/'equation247_weak');ap.add_argument('--receipt',type=Path)
    args=ap.parse_args();d=load(args.endpoint)
    ans={'status':'PASS','metrics':check(d),'corruption_controls':controls(d),
         'scope':'Exact source delta, inherited independent Horn replay, integral projection, translation, and complete SOS collection; unbounded semantics require the written proof.'}
    s=json.dumps(ans,sort_keys=True,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(s)
    print(s,end='')
