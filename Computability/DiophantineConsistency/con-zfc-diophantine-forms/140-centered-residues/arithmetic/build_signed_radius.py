#!/usr/bin/env python3
"""Replace eleven signed remainder guards by four centered radius caps.

All variables are unrestricted integers. The arithmetic proof is in
SIGNED_RADIUS_PROOF.md. This compiler performs the finite source mutation,
then emits and independently replays monic degree-preserving projections.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,sys

HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'vendor'))
import terminal_elimination as E
import round15_independent_algebra as A
import translate_coordinates as T

def read(p):return json.loads(p.read_text())
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(E.canonical_bytes(x))
def need(b,msg):
    if not b:raise ValueError(msg)

def transform(source,meta,odd_square=False,weighted=False):
    rows=source['residuals'];vs=source['variables'];names={v['name']:i for i,v in enumerate(vs)}
    deleted_rows=set();deleted_vars=set();groups={};records=[]
    for g in meta['guards']:
        if g['kind']!='postsemantic_interval':continue
        remainder,slack=g['pair']
        rid=[i for i,r in enumerate(rows) if r['label'].endswith('.remainder_bound') and
             E.normalize(r['terms']).get((remainder,))==-1 and E.normalize(r['terms']).get((slack,))==-1]
        need(len(rid)==1,'interval bound mismatch');rid=rid[0]
        plus=[m[0] for c,m in rows[rid]['terms'] if c==1 and len(m)==1]
        need(len(plus)==1,'no unique denominator');den=plus[0]
        need(E.normalize(rows[rid]['terms'])=={():-1,(den,):1,(remainder,):-1,(slack,):-1},'bound shape')
        guardpoly={(min(remainder,slack),max(remainder,slack)):1}
        a,b,c=g['auxiliary']
        for v in [a,b,c]:guardpoly[(v,v)]=-1
        guardpoly[(c,)]=-1
        guard=[i for i,r in enumerate(rows) if E.normalize(r['terms'])==guardpoly]
        need(len(guard)==1,'unique product guard')
        deleted_rows.update([rid,guard[0]]);deleted_vars.update([slack,a,b,c])
        rec=dict(bound_row=rid,guard_row=guard[0],remainder=remainder,slack=slack,
                 auxiliary=[a,b,c],denominator=den,label=rows[rid]['label'])
        groups.setdefault(den,[]).append(rec);records.append(rec)
    need(sorted(map(len,groups.values()))==[2,2,2,5],'group census')
    odd=None
    if odd_square:
        outrow=[i for i,r in enumerate(rows)if r['label']=='choose0.digit_bound']
        need(len(outrow)==1,'output bound census');outrow=outrow[0]
        o=next(i for i,v in enumerate(vs)if v['name']=='choose0.oslack')
        g=next(g for g in meta['guards']if g['kind']=='front_nonnegative' and g['coordinate']==o)
        guardpoly={(o,):1}
        for v in g['auxiliary']:guardpoly[(v,v)]=-1
        guardpoly[(g['auxiliary'][2],)]=-1
        grow=[i for i,r in enumerate(rows)if E.normalize(r['terms'])==guardpoly]
        need(len(grow)==1,'output sign guard census')
        qp=[m[0]for c,m in rows[outrow]['terms']if c==1 and len(m)==1]
        need(len(qp)==1,'output radix coordinate');q=qp[0]
        deleted_rows.update([outrow,grow[0]]);deleted_vars.update([o]+g['auxiliary'])
        odd=dict(q=q,old_slack=o,old_auxiliary=g['auxiliary'],old_bound_row=outrow,old_guard_row=grow[0])
    for v in deleted_vars:
        occ={i for i,r in enumerate(rows) if any(v in m for c,m in r['terms'])}
        need(occ<=deleted_rows,'deleted private coordinate used outside deleted rows')
    retained=[i for i in range(len(vs)) if i not in deleted_vars]
    ren={v:i for i,v in enumerate(retained)}
    out=copy.deepcopy(source);out['variables']=[copy.deepcopy(vs[i])for i in retained]
    out['residuals']=[dict(label=r['label'],terms=[[c,[ren[i]for i in m]]for c,m in r['terms']])
                      for j,r in enumerate(rows) if j not in deleted_rows]
    caps=[]
    if odd is not None:
        z=len(out['variables']);out['variables'].append(dict(kind='signed_witness',name='radix.odd_square_root_half'))
        odd['new_root']=z;odd['new_row']=len(out['residuals'])
        out['residuals'].append(dict(label='radix.odd_square',terms=E.as_terms(E.normalize([[1,[ren[q]]],[-4,[z,z]],[-4,[z]],[-1,[]]]))))
    capgroups=[(d,[(r,1)for r in rs])for d,rs in sorted(groups.items())]
    weighted_info=None
    if weighted:
        qrow=next(r for r in rows if r['label']=='choose0.digit_bound')
        q=next(m[0]for c,m in qrow['terms']if c==1 and len(m)==1)
        dlo=next(d for d,rs in groups.items()if any(r['label']=='choose0.remainder_bound'for r in rs))
        dhi=next(d for d,rs in groups.items()if any(r['label']=='crt.range.a.remainder_bound'for r in rs))
        calls=meta['square_budget']['power_calls']
        lowcall=next(p for p in calls if p['output']==[[1,[dlo]]])
        highcall=next(p for p in calls if p['output']==[[1,[dhi]]])
        need(lowcall['base']==highcall['base']==[[1,[q]]],'weighted powers use different bases')
        ediff=A.add(A.norm(highcall['exponent']),A.sc(A.norm(lowcall['exponent']),-1))
        need(ediff=={():1},'weighted denominator exponents are not consecutive')
        capgroups=[(d,rs)for d,rs in capgroups if d not in [dlo,dhi]]
        capgroups.insert(0,(dhi,[(r,q)for r in groups[dlo]]+[(r,1)for r in groups[dhi]]))
        weighted_info=dict(q=q,lower_denominator=dlo,upper_denominator=dhi,
                           lower_power_call=lowcall,upper_power_call=highcall,
                           identity='D_upper=q*D_lower follows after exact power recovery')
    for j,(d,weighted_rs) in enumerate(capgroups):
        rs=[r for r,w in weighted_rs]
        residue_coordinates=[];products=[]
        for r,w in weighted_rs:
            if w==1:residue_coordinates.append(ren[r['remainder']]);continue
            v=len(out['variables']);out['variables'].append(dict(kind='gate',name='radius.weighted.'+str(r['remainder'])))
            products.append(dict(source_remainder=r['remainder'],source_weight=w,variable=v,row=len(out['residuals'])))
            out['residuals'].append(dict(label='radius.weighted_product.'+str(r['remainder']),terms=E.as_terms(E.normalize([[1,[v]],[-1,[ren[w],ren[r['remainder']]]]]))))
            residue_coordinates.append(v)
        av=[]
        for role in ['a','b','c']:
            av.append(len(out['variables']));out['variables'].append(dict(kind='integer_guard',name=f'radius{j}.{role}'))
        a,b,c=av
        terms=[[1,[ren[d],ren[d]]],[-1,[]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]
        terms += [[-4,[v,v]] for v in residue_coordinates]
        row=dict(label=f'centered_remainder_radius.{j}',terms=E.as_terms(E.normalize(terms)))
        caps.append(dict(denominator_source=d,remainder_sources=[r['remainder']for r in rs],auxiliary=av,row=len(out['residuals']),
                         residue_coordinates=residue_coordinates,products=products))
        out['residuals'].append(row)
    out['variant']='cofinal_signed_centered_remainder_radius'
    out.pop('metrics',None)
    cert=dict(schema='centered_remainder_radius/v1',source_sha256=A.sha(source),target_sha256=A.sha(out),
              retained_source_variables=retained,retained_source_rows=[i for i in range(len(rows))if i not in deleted_rows],
              removed_variables=sorted(deleted_vars),removed_rows=sorted(deleted_rows),records=records,caps=caps,odd_square=odd,weighted=weighted_info,
              theorem='Canonical low digits lie below D/15. The radius row forces |r|<D/2 and hence r is the unique canonical representative.')
    return out,cert

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--support-cap',type=int,default=16);p.add_argument('--odd-square',action='store_true');p.add_argument('--weighted',action='store_true');args=p.parse_args()
    src=read(HERE/'signed_source/factored_source.json');meta=read(HERE/'signed_source/transform_certificate.json')
    raw,rc=transform(src,meta,args.odd_square,args.weighted)
    projected,pc,metrics=E.optimize(raw,max_support=args.support_cap)
    A.projection(raw,projected,pc)
    old=read(HERE/'signed_source/projected.json');oldtc=read(HERE/'signed_source/translation_certificate.json')
    shifts_by_name={old['variables'][v]['name']:d for v,d in oldtc['shifts']}
    shifts={v:shifts_by_name[m['name']] for v,m in enumerate(projected['variables']) if m['name'] in shifts_by_name}
    final=T.translate(projected,shifts)
    final['variant']+=':inherited_coordinate_shifts'
    poly=E.expand(final);independent,used=A.literal(final)
    need(poly['terms']==A.terms(independent),'expansion mismatch');need(used==set(range(len(final['variables']))),'unused coordinate')
    tc=dict(schema='integral_translation_v1',input_sha256=A.sha(projected),output_sha256=A.sha(final),shifts=sorted(shifts.items()),convention='old=new+shift')
    met=dict(variables=len(final['variables']),rows=len(final['residuals']),degree=max(len(m)for c,m in poly['terms']),
             monomials=len(poly['terms']),height=max(abs(c)for c,m in poly['terms']),row_height=max(abs(c)for r in final['residuals']for c,m in r['terms']))
    for name,obj in [('raw_equation.json',raw),('radius_certificate.json',rc),('projected.json',projected),('projection.json',pc),
                     ('equation.json',final),('expanded_polynomial.json',poly),('translation.json',tc),('metrics.json',met)]:write(args.output/name,obj)
    print(json.dumps(met,indent=2))

if __name__=='__main__':main()
