#!/usr/bin/env python3
"""Independent exact check of pooled low-digit bounds and natural projections."""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,importlib.util,json,sys

HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'vendor'))
import round15_independent_algebra as A

def read(p):return json.loads(p.read_text())
def need(b,msg):
    if not b:raise ValueError(msg)
def sha(x):return hashlib.sha256(A.canon(x).rstrip(b'\n')).hexdigest()

def mutation(source,raw,cert):
    need(source['domain']==raw['domain']=='nonnegative integers','domain')
    need(sha(source)==cert['source_sha256']and sha(raw)==cert['target_sha256'],'mutation hashes')
    need(cert.get('weighted')is None,'selected natural forms use unweighted pools')
    vs=source['variables'];rows=source['residuals'];names={v['name']:i for i,v in enumerate(vs)}
    groups={}
    for i,row in enumerate(rows):
        if not row['label'].endswith('.remainder_bound')or row['label']=='fact0.remainder_bound':continue
        tag=row['label'][:-len('.remainder_bound')];r=names[tag+'.modular_remainder'];s=names[tag+'.modular_rslack']
        d=[m[0]for c,m in row['terms']if c==1 and len(m)==1];need(len(d)==1,'unique denominator');d=d[0]
        need(A.norm(row)=={():-1,(d,):1,(r,):-1,(s,):-1},'old interval row')
        groups.setdefault(d,[]).append(dict(row=i,label=tag,remainder=r,slack=s))
    need(sorted(map(len,groups.values()))==[2,2,2,5],'group census')
    gone=set();removed=set();replacements={};expected_groups=[]
    for j,(d,rs)in enumerate(sorted(groups.items())):
        pivot=rs[0];p=A.add(A.v(d),A.con(-1),A.sc(A.v(pivot['slack']),-1))
        for r in rs:p=A.add(p,A.sc(A.v(r['remainder']),-1))
        replacements[pivot['row']]=dict(label=f'pooled.low_digits.{j}',terms=A.terms(p))
        for r in rs[1:]:gone.add(r['slack']);removed.add(r['row'])
        expected_groups.append(dict(denominator=d,pivot=pivot,members=rs,restoration='old_slack = pooled_slack + sum(other remainders)'))
    need(cert['groups']==expected_groups,'group records')
    digit=cert['digit_bound'];need(digit is not None,'selected endpoint drops derived output bound')
    o=names['choose0.modular_oslack'];rid=next(i for i,r in enumerate(rows)if r['label']=='choose0.digit_bound')
    need(digit==dict(row=rid,slack=o,deleted_residual=rows[rid],restoration='q - B - 1',justification='power bootstrap q >= B^4 > B >= 2'),'output-bound record')
    gone.add(o);removed.add(rid)
    for v in gone:need(all(i in removed for i,row in enumerate(rows)if any(v in m for c,m in row['terms'])),'removed coordinate not private')
    keep=[i for i in range(len(vs))if i not in gone];ren={v:i for i,v in enumerate(keep)}
    need(cert['removed_rows']==sorted(removed)and cert['removed_variables']==sorted(gone)and cert['retained_original_indices']==keep,'deletion maps')
    rowids=cert['retained_original_row_indices'];expected_ids=[i for i in range(len(rows))if i not in removed]
    need(sorted(rowids)==expected_ids,'row permutation census')
    priority=read(HERE/'source/row_priority.json');priority_ids=sorted(expected_ids,key=lambda i:priority[i])
    need(rowids in [expected_ids,priority_ids],'unrecognized selected row order')
    expected_vars=deepcopy([vs[i]for i in keep])
    for j,(d,rs)in enumerate(sorted(groups.items())):expected_vars[ren[rs[0]['slack']]]['name']=f'pooled.low_digits.{j}.slack'
    expected=[]
    for i in rowids:
        r=replacements.get(i,rows[i]);expected.append(dict(label=r['label'],terms=[[c,[ren[v]for v in m]]for c,m in r['terms']]))
    need(expected_vars==raw['variables']and expected==raw['residuals'],'complete pooled raw system')
    return dict(groups=4,old_remainders=11,removed_coordinates=len(gone),removed_rows=len(removed))

def check_endpoint(path,controls=False):
    src=read(HERE/'source/equation.json');raw=read(path/'raw_equation.json');tc=read(path/'transformation.json')
    change=mutation(src,raw,tc);eq=read(path/'equation.json');pc=read(path/'projection.json')
    steps=A.projection(raw,eq,pc,natural=True)
    poly,used=A.literal(eq);xp=read(path/'expanded_polynomial.json')
    need(A.terms(poly)==xp['terms'],'every expanded coefficient')
    need(used==set(range(len(eq['variables']))),'all coordinates live')
    met=dict(variables=len(eq['variables']),rows=len(eq['residuals']),degree=max(map(len,poly)),monomials=len(poly),height=max(map(abs,poly.values())))
    recorded=read(path/'metrics.json')
    need((met['variables'],met['rows'],met['degree'],met['monomials'],met['height'])==(recorded['variables'],recorded['rows'],recorded['exact_degree'],recorded['expanded_monomials'],recorded['coefficient_height']),'exact metrics')
    n=0
    if controls:
        bad=deepcopy(raw);bad['residuals'][0]['terms'][0][0]+=1;bc=deepcopy(tc);bc['target_sha256']=sha(bad)
        try:mutation(src,bad,bc)
        except ValueError:n+=1
        else:raise ValueError('corrupted raw row accepted')
        bad=deepcopy(pc);bad['steps'][0]['restoration'][0][0]+=1
        try:A.projection(raw,eq,bad,natural=True)
        except ValueError:n+=1
        else:raise ValueError('corrupted natural restoration accepted')
        bad=deepcopy(xp);bad['terms'][0][0]+=1;need(bad['terms']!=A.terms(poly),'coefficient corruption accepted');n+=1
    return dict(path=path.name,metrics=met,change=change,projection_steps=steps,negative_controls_rejected=n,equation_sha256=hashlib.sha256((path/'equation.json').read_bytes()).hexdigest())

def main():
    p=argparse.ArgumentParser();p.add_argument('paths',nargs='*',type=Path);p.add_argument('--receipt',type=Path);p.add_argument('--negative-controls',action='store_true');a=p.parse_args()
    paths=a.paths or [HERE/'natural222',HERE/'natural221_high',HERE/'natural223_sparse']
    out=dict(status='PASS',optimized=bool(sys.flags.optimize),endpoints=[check_endpoint(p,a.negative_controls)for p in paths],scope='complete raw transformation, certified nonnegative projections and every collected quartic coefficient')
    if a.receipt:a.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
