#!/usr/bin/env python3
"""Replace eleven postsemantic interval guards by one common centered budget.

The algebra is finite and the semantic bridge is proved separately. This script
does not search for a zero or assume Con(ZFC).
"""
from pathlib import Path
import sys, json, copy, hashlib, argparse
RUNTIME=Path(__file__).resolve().parent
sys.path.insert(0,str(RUNTIME))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T
add,neg,V=F.add,F.neg,F.V
mul=E.multiply

def put(d,n,x):
    d.mkdir(parents=True,exist_ok=True)
    (d/n).write_bytes(E.canonical_bytes(x))
def sha(x):return hashlib.sha256(E.canonical_bytes(x)).hexdigest()
def scale(p,k):return {m:k*c for m,c in p.items()}

def build(source_dir,out,cap=16,group_mode=True,scale_digits=False):
    source=json.loads((source_dir/'source.json').read_text())
    cert=json.loads((source_dir/'transform_certificate.json').read_text())
    original=copy.deepcopy(source)
    guards=[g for g in cert['guards'] if g['kind']!='postsemantic_interval']
    intervals=[g for g in cert['guards'] if g['kind']=='postsemantic_interval']
    if len(intervals)!=11:raise ValueError('Expected eleven interval guards')
    names={v['name']:i for i,v in enumerate(source['variables'])}
    groups={}
    remove_rows=set()
    for g in intervals:
        row=source['residuals'][g['bound_row']]
        p=E.normalize(row['terms']);r,s=g['pair']
        p=add(p,V(r),V(s),{():1})
        if len(p)!=1:raise ValueError('Not a one-coordinate denominator')
        (mon,c),=p.items()
        if len(mon)!=1 or c!=1:raise ValueError('Not positive unit denominator')
        L=mon[0]
        groups.setdefault(L,[]).append(r)
        remove_rows.add(g['bound_row'])
    M=names['pow14.output']
    if sorted(len(g) for g in groups.values())!=[2,2,2,5] or M not in groups:
        raise ValueError('Unexpected interval groups')
    source['residuals']=[r for i,r in enumerate(source['residuals']) if i not in remove_rows]
    additions=[]
    def var(n,kind='signed_witness'):
        i=len(source['variables']);source['variables'].append({'name':'remainder_budget.'+n,'kind':kind});return i
    def row(n,p):
        if E.degree(p)>2:raise ValueError('Nonquadratic '+n)
        r={'label':'remainder_budget.'+n,'terms':E.as_terms(p)}
        source['residuals'].append(r);additions.append(r)
    def gate(n,p):
        i=var(n,'gate');row(n,add(V(i),neg(p)));return i
    budget={};group_certs=[];ratio_map={};digit_changes=[]
    for j,(L,rems) in enumerate(sorted(groups.items())):
        ss=add(*[mul(V(r),V(r)) for r in rems])
        if L==M:
            budget=add(budget,ss)
            group_certs.append({'denominator':L,'remainders':rems,'ratio':None,'mode':'identity'})
            continue
        v=var('ratio'+str(j));row('ratio'+str(j),add(V(M),neg(mul(V(L),V(v)))))
        ratio_map[L]=v
        if scale_digits:
            budget=add(budget,ss)
            group_certs.append({'denominator':L,'remainders':rems,'ratio':v,'mode':'rescaled_coordinates'})
            continue
        if group_mode and len(rems)>=3:
            a=gate('sum_squares'+str(j),ss)
            b=gate('ratio_square'+str(j),mul(V(v),V(v)))
            c=gate('weighted_sum'+str(j),mul(V(a),V(b)))
            budget=add(budget,V(c))
            group_certs.append({'denominator':L,'remainders':rems,'ratio':v,'mode':'group','sum':a,'square':b,'product':c})
        else:
            zs=[gate('scaled'+str(j)+'_'+str(k),mul(V(v),V(r))) for k,r in enumerate(rems)]
            budget=add(budget,*[mul(V(z),V(z)) for z in zs])
            group_certs.append({'denominator':L,'remainders':rems,'ratio':v,'mode':'individual','scaled':zs})
    if scale_digits:
        N=names['pow1.output']
        def defining_product(a,b):
            wanted=mul(V(a),V(b))
            for ri,rr in enumerate(source['residuals']):
                pp=E.normalize(rr['terms'])
                for mm,cc in pp.items():
                    if len(mm)==1 and E.candidate(pp,mm[0],False)==wanted:
                        return ri,mm[0]
            raise ValueError(('Missing product',a,b))
        common_row,common_product=defining_product(N,M)
        alias={};alias_rows=set()
        for L in groups:
            if L==M:continue
            ri,old=defining_product(N,L)
            alias[old]=common_product;alias_rows.add(ri)
        for L,rems in groups.items():
            for rem in rems:
                hits=[(i,r) for i,r in enumerate(source['residuals']) if any(rem in mm for _,mm in r['terms'])]
                if len(hits)!=1:raise ValueError(('Remainder nonlocal',rem,hits))
                ri,rr=hits[0];pp=E.normalize(rr['terms'])
                us=[mm[0] for mm,cc in pp.items() if cc==1 and len(mm)==1 and source['variables'][mm[0]]['name'].startswith('pow')]
                if len(us)!=1:raise ValueError(('Numerator shape',rr))
                u=us[0]
                if L!=M:
                    pp=add(pp,neg(V(u)),mul(V(ratio_map[L]),V(u)))
                    nr=dict(rr,terms=E.as_terms(pp));source['residuals'][ri]=nr
                    digit_changes.append({'kind':'scaled_numerator','row':ri,'old':rr,'new':nr,'ratio':ratio_map[L],'remainder':rem})
                source['variables'][rem]['name']='normalized.'+source['variables'][rem]['name']
                if rr['label']=='choose0.digit':
                    zs=[mm[0] for mm,cc in E.normalize(rr['terms']).items() if cc==-1 and len(mm)==1 and mm[0]!=rem]
                    if len(zs)!=1:raise ValueError('Choose product shape')
                    z=zs[0]
                    ds=[(i,r) for i,r in enumerate(source['residuals']) if r['label']=='multiplication' and E.candidate(E.normalize(r['terms']),z,False) is not None]
                    if len(ds)!=1:raise ValueError('Choose product definition')
                    di,dr=ds[0];newp=E.substitute(E.normalize(dr['terms']),L,V(M))
                    nr=dict(dr,terms=E.as_terms(newp));source['residuals'][di]=nr
                    digit_changes.append({'kind':'scaled_choose_denominator','row':di,'old':dr,'new':nr})
        newrows=[]
        for ri,rr in enumerate(source['residuals']):
            if ri in alias_rows:
                digit_changes.append({'kind':'delete_denominator_product','row':ri,'old':rr});continue
            pp=E.normalize(rr['terms'])
            for old,new in alias.items():pp=E.substitute(pp,old,V(new))
            nr=dict(rr,terms=E.as_terms(pp))
            if nr!=rr:digit_changes.append({'kind':'alias_denominator_product','row':ri,'old':rr,'new':nr})
            newrows.append(nr)
        source['residuals']=newrows
    new_guard={'kind':'centered_remainder_budget','expression':E.as_terms(add(mul(V(M),V(M)),{():-1},scale(budget,-4)))}
    guards.append(new_guard)
    guarded=copy.deepcopy(source)
    guard_records=[]
    for j,g0 in enumerate(guards):
        g={k:v for k,v in g0.items() if k not in ('row','auxiliary')}
        aux=list(range(len(guarded['variables']),len(guarded['variables'])+3));a,b,c=aux
        guarded['variables'] += [{'name':f'new_guard{j}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        p=add(E.normalize(g['expression']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
        g.update({'auxiliary':aux,'row':len(guarded['residuals'])})
        guarded['residuals'].append({'label':f'domain_guard.{j}','terms':E.as_terms(p)})
        guard_records.append(g)
    guarded['variant']+=':shared_centered_remainders'
    factored,fc=F.transform(guarded)
    projected,pc,metrics=E.optimize(factored,max_support=cap)
    check=E.verify(factored,projected,pc)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
    for i,v in enumerate(projected['variables']):
        if v['name']=='t0':shifts[i]=-16
    final=T.translate(projected,shifts);poly=E.expand(final)
    metric={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),'guards':len(guards)}
    transformation={'schema':'shared_centered_remainders_v1','parent_source_sha256':sha(original),'parent_transform_sha256':sha(cert),'deleted_bound_rows':sorted(remove_rows),'old_interval_guards':intervals,'new_groups':group_certs,'new_guards':guard_records,'budget':E.as_terms(budget),'common_denominator':M,'added_rows':additions,'source_sha256':sha(source),'guarded_sha256':sha(guarded),'digit_changes':digit_changes,'rescaled_coordinates':scale_digits}
    trans={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(final),'shifts':[[i,s] for i,s in shifts.items()],'convention':'old=new+shift'}
    for name,obj in [('parent_source.json',original),('parent_transform_certificate.json',cert),('source.json',source),('guarded.json',guarded),('remainder_transformation.json',transformation),('factored_source.json',factored),('factorization_certificate.json',fc),('projected.json',projected),('projection_certificate.json',pc),('PROJECTION_CHECK.json',check),('translation_certificate.json',trans),('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',metric)]:put(out,name,obj)
    print(json.dumps(metric,indent=2))
    return metric

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('out',type=Path);p.add_argument('--cap',type=int,default=16);p.add_argument('--individual',action='store_true');p.add_argument('--scale-digits',action='store_true')
    a=p.parse_args();build(RUNTIME.parent/'upstream'/'parent',a.out,a.cap,not a.individual,a.scale_digits)
