#!/usr/bin/env python3
"""Independently check radius/odd-square mutations and all final coefficients.

This checker imports the retained independent algebra library, never the new
producer. It authenticates finite algebra, not the unbounded arithmetic proof.
"""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json,sys

HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'vendor'))
import round15_independent_algebra as A

def need(b,msg):
    if not b:raise ValueError(msg)
def read(p):return json.loads(p.read_text())

def mutation(source,meta,raw,cert):
    need(source['domain']==raw['domain']=='unrestricted integers','domains')
    need(A.sha(source)==cert['source_sha256'] and A.sha(raw)==cert['target_sha256'],'mutation hash binding')
    rows=source['residuals'];variables=source['variables'];deletions=set();gone=set();groups={}
    for g in meta['guards']:
        if g['kind']!='postsemantic_interval':continue
        r,s=g['pair'];a,b,c=g['auxiliary']
        hits=[]
        for i,row in enumerate(rows):
            p=A.norm(row)
            if row['label'].endswith('.remainder_bound') and p.get((r,))==-1 and p.get((s,))==-1:
                d=[m[0]for m,x in p.items()if x==1 and len(m)==1]
                need(len(d)==1,'denominator census');d=d[0]
                need(p=={():-1,(d,):1,(r,):-1,(s,):-1},'exact old bound')
                hits.append((i,d,row['label']))
        need(len(hits)==1,'unique old bound');rid,d,label=hits[0]
        gp=A.add(A.mul(A.v(r),A.v(s)),A.sc(A.add(A.mul(A.v(a),A.v(a)),A.mul(A.v(b),A.v(b)),A.mul(A.v(c),A.v(c)),A.v(c)),-1))
        gi=[i for i,row in enumerate(rows)if A.norm(row)==gp]
        need(len(gi)==1,'unique old product guard')
        rec=dict(bound_row=rid,guard_row=gi[0],remainder=r,slack=s,auxiliary=[a,b,c],denominator=d,label=label)
        groups.setdefault(d,[]).append(rec);deletions.update([rid,gi[0]]);gone.update([s,a,b,c])
    need(sorted(map(len,groups.values()))==[2,2,2,5],'eleven intervals/four denominators')
    need(cert['records']==[r for g in meta['guards']if g['kind']=='postsemantic_interval' for rs in groups.values()for r in rs if r['remainder']==g['pair'][0]],'interval record order')
    qbound=next((i,row)for i,row in enumerate(rows)if row['label']=='choose0.digit_bound')
    q=next(m[0]for c,m in qbound[1]['terms']if c==1 and len(m)==1)
    odd=cert.get('odd_square')
    if odd is not None:
        o=next(i for i,v in enumerate(variables)if v['name']=='choose0.oslack')
        g=next(g for g in meta['guards']if g['kind']=='front_nonnegative' and g['coordinate']==o)
        a,b,c=g['auxiliary']
        gp=A.add(A.v(o),A.sc(A.add(A.mul(A.v(a),A.v(a)),A.mul(A.v(b),A.v(b)),A.mul(A.v(c),A.v(c)),A.v(c)),-1))
        gi=[i for i,row in enumerate(rows)if A.norm(row)==gp];need(len(gi)==1,'old output guard')
        need({k:odd[k]for k in ['q','old_slack','old_auxiliary','old_bound_row','old_guard_row']}==dict(q=q,old_slack=o,old_auxiliary=[a,b,c],old_bound_row=qbound[0],old_guard_row=gi[0]),'odd square record')
        deletions.update([qbound[0],gi[0]]);gone.update([o,a,b,c])
    for v in gone:
        need(all(i in deletions for i,row in enumerate(rows)if any(v in m for c,m in row['terms'])),'nonprivate deleted variable')
    keep=[i for i in range(len(variables))if i not in gone];ren={v:i for i,v in enumerate(keep)}
    keep_rows=[i for i in range(len(rows))if i not in deletions]
    need(cert['retained_source_variables']==keep and cert['retained_source_rows']==keep_rows,'retained coordinate/row maps')
    need(cert['removed_variables']==sorted(gone) and cert['removed_rows']==sorted(deletions),'deletion census')
    expected_vars=deepcopy([variables[i]for i in keep])
    expected_rows=[dict(label=rows[i]['label'],terms=[[c,[ren[v]for v in m]]for c,m in rows[i]['terms']])for i in keep_rows]
    if odd is not None:
        z=len(expected_vars);need(odd['new_root']==z and odd['new_row']==len(expected_rows),'odd coordinate placement')
        expected_vars.append(dict(kind='signed_witness',name='radix.odd_square_root_half'))
        expected_rows.append(dict(label='radix.odd_square',terms=A.terms(A.add(A.v(ren[q]),A.sc(A.mul(A.v(z),A.v(z)),-4),A.sc(A.v(z),-4),A.con(-1)))))
    capgroups=[(d,[(r,1)for r in rs])for d,rs in sorted(groups.items())]
    weighted=cert.get('weighted')
    if weighted is not None:
        dlo=next(d for d,rs in groups.items()if any(r['label']=='choose0.remainder_bound'for r in rs))
        dhi=next(d for d,rs in groups.items()if any(r['label']=='crt.range.a.remainder_bound'for r in rs))
        lc=next(c for c in meta['square_budget']['power_calls']if c['output']==[[1,[dlo]]])
        hc=next(c for c in meta['square_budget']['power_calls']if c['output']==[[1,[dhi]]])
        need(lc['base']==hc['base']==[[1,[q]]],'consecutive-power common base')
        need(A.add(A.norm(hc['exponent']),A.sc(A.norm(lc['exponent']),-1))==A.con(1),'consecutive powers')
        need(weighted==dict(q=q,lower_denominator=dlo,upper_denominator=dhi,lower_power_call=lc,upper_power_call=hc,identity='D_upper=q*D_lower follows after exact power recovery'),'weighted identity record')
        capgroups=[g for g in capgroups if g[0]not in [dlo,dhi]]
        capgroups.insert(0,(dhi,[(r,q)for r in groups[dlo]]+[(r,1)for r in groups[dhi]]))
    expected_caps=[]
    for j,(d,rs)in enumerate(capgroups):
        coords=[];products=[]
        for r,w in rs:
            if w==1:coords.append(ren[r['remainder']]);continue
            v=len(expected_vars);expected_vars.append(dict(kind='gate',name='radius.weighted.'+str(r['remainder'])))
            products.append(dict(source_remainder=r['remainder'],source_weight=w,variable=v,row=len(expected_rows)))
            expected_rows.append(dict(label='radius.weighted_product.'+str(r['remainder']),terms=A.terms(A.add(A.v(v),A.sc(A.mul(A.v(ren[w]),A.v(ren[r['remainder']])),-1)))))
            coords.append(v)
        av=[]
        for role in ['a','b','c']:
            av.append(len(expected_vars));expected_vars.append(dict(kind='integer_guard',name=f'radius{j}.{role}'))
        a,b,c=av
        p=A.add(A.mul(A.v(ren[d]),A.v(ren[d])),A.con(-1),A.sc(A.v(c),-1))
        for v in av:p=A.add(p,A.sc(A.mul(A.v(v),A.v(v)),-1))
        for v in coords:p=A.add(p,A.sc(A.mul(A.v(v),A.v(v)),-4))
        expected_caps.append(dict(denominator_source=d,remainder_sources=[r['remainder']for r,w in rs],auxiliary=av,row=len(expected_rows),residue_coordinates=coords,products=products))
        expected_rows.append(dict(label=f'centered_remainder_radius.{j}',terms=A.terms(p)))
    need(expected_caps==cert['caps'],'cap metadata')
    need(expected_vars==raw['variables'],'complete new coordinate list')
    need(expected_rows==raw['residuals'],'every changed/unchanged row')
    return dict(removed_intervals=11,radius_caps=len(expected_caps),new_gap_coordinates=3*len(expected_caps),odd_square=odd is not None,weighted=weighted is not None)

def check_endpoint(path,negative_controls=False):
    src=read(HERE/'signed_source/factored_source.json');meta=read(HERE/'signed_source/transform_certificate.json')
    raw=read(path/'raw_equation.json');rc=read(path/'radius_certificate.json')
    stats=mutation(src,meta,raw,rc)
    projected=read(path/'projected.json');pc=read(path/'projection.json')
    steps=A.projection(raw,projected,pc)
    eq=read(path/'equation.json');tc=read(path/'translation.json')
    need(A.sha(projected)==tc['input_sha256']and A.sha(eq)==tc['output_sha256'],'translation hashes')
    shifts=dict(tc['shifts']);need(len(shifts)==len(tc['shifts']),'duplicate translations')
    expected=[]
    for row in projected['residuals']:
        p=A.norm(row)
        for v,d in shifts.items():p=A.sub(p,v,A.add(A.v(v),A.con(d)))
        expected.append(dict(label=row['label'],terms=A.terms(p)))
    need(eq['residuals']==expected and eq['variables']==projected['variables'],'complete translated polynomial')
    poly,used=A.literal(eq);expanded=read(path/'expanded_polynomial.json')
    need(expanded['terms']==A.terms(poly),'every collected coefficient')
    need(used==set(range(len(eq['variables']))),'all coordinates live')
    met=dict(variables=len(eq['variables']),rows=len(eq['residuals']),degree=max(map(len,poly)),monomials=len(poly),height=max(map(abs,poly.values())),row_height=max(abs(c)for r in eq['residuals']for c,m in r['terms']))
    need(met==read(path/'metrics.json'),'exact metric record')
    controls=0
    if negative_controls:
        bad=deepcopy(raw);cap=rc['caps'][0];bad['residuals'][cap['row']]['terms'][0][0]+=1
        cr=deepcopy(rc);cr['target_sha256']=A.sha(bad)
        try:mutation(src,meta,bad,cr)
        except ValueError:controls+=1
        else:raise ValueError('corrupted radius accepted')
        badcert=deepcopy(rc);badcert['removed_variables']=badcert['removed_variables'][:-1]
        try:mutation(src,meta,raw,badcert)
        except ValueError:controls+=1
        else:raise ValueError('corrupted deletion census accepted')
        badproj=deepcopy(pc);badproj['steps'][0]['restoration'][0][0]+=1
        try:A.projection(raw,projected,badproj)
        except ValueError:controls+=1
        else:raise ValueError('corrupted restoration accepted')
        badpoly=deepcopy(expanded);badpoly['terms'][0][0]+=1
        need(badpoly['terms']!=A.terms(poly),'coefficient corruption undetected');controls+=1
    return dict(path=path.name,metrics=met,mutation=stats,projection_steps=steps,negative_controls_rejected=controls,equation_sha256=hashlib.sha256((path/'equation.json').read_bytes()).hexdigest())

def main():
    p=argparse.ArgumentParser();p.add_argument('paths',nargs='*',type=Path);p.add_argument('--receipt',type=Path);p.add_argument('--negative-controls',action='store_true');args=p.parse_args()
    paths=args.paths or [HERE/'signed258',HERE/'signed259',HERE/'audit261']
    out=dict(status='PASS',optimized=bool(sys.flags.optimize),endpoints=[check_endpoint(p,args.negative_controls)for p in paths],scope='exact mutation, all monic substitutions, all translations and all quartic coefficients')
    if args.receipt:args.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
