#!/usr/bin/env python3
"""Pool four low-digit budgets in the cofinal-anchor graph.

The graph is a literal mutation of the retained normalized quadratic source.
Every coordinate remains nonnegative. The only semantic deletion is the
redundant binomial-output bound, proved in PROOF.md; other old private slacks
have explicit nonnegative polynomial restorations.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def load(name):
    spec=importlib.util.spec_from_file_location('direct_'+name,HERE/'vendor'/(name+'.py'))
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m

contract=load('contract')
check=load('check')

def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')

def transform(source, drop_digit=True, ordered=False, weighted=False):
    rows=source['residuals']
    variables=source['variables']
    source_name={v['name']:i for i,v in enumerate(variables)}
    groups={}
    for rid,row in enumerate(rows):
        if row['label'].endswith('.remainder_bound') and row['label']!='fact0.remainder_bound':
            tag=row['label'].removesuffix('.remainder_bound')
            remainder=source_name[tag+'.modular_remainder']
            slack=source_name[tag+'.modular_rslack']
            plus=[m[0] for c,m in row['terms'] if c==1 and len(m)==1]
            if len(plus)!=1: raise ValueError('noncanonical remainder row')
            den=plus[0]
            if contract.loadpoly(row['terms'])!={():-1,(den,):1,(remainder,):-1,(slack,):-1}:
                raise ValueError('unexpected remainder row')
            groups.setdefault(den,[]).append(dict(row=rid,label=tag,remainder=remainder,slack=slack))
    if sorted(len(g) for g in groups.values())!=[2,2,2,5]:
        raise ValueError('wrong group census')
    deleted_rows=set();deleted_vars=set();replacements={};cert=[]
    for group_no,(den,members) in enumerate(sorted(groups.items())):
        pivot=members[0]
        newpoly={():-1,(den,):1,(pivot['slack'],):-1}
        for m in members:newpoly[(m['remainder'],)]=-1
        replacements[pivot['row']]=dict(label='pooled.low_digits.'+str(group_no),terms=contract.dump(newpoly))
        for m in members[1:]:
            deleted_rows.add(m['row']);deleted_vars.add(m['slack'])
        cert.append(dict(denominator=den,pivot=pivot,members=members,
                         restoration='old_slack = pooled_slack + sum(other remainders)'))
    weighted_cert=None
    if weighted:
        q=source_name['pow2.output']
        lowden=next(d for d,ms in groups.items() if any(m['label']=='choose0' for m in ms))
        highden=next(d for d,ms in groups.items() if any(m['label']=='crt.range.a' for m in ms))
        lows=groups[lowden];highs=groups[highden]
        expected={(highden,):1,tuple(sorted((q,lowden))):-1}
        if not any(contract.loadpoly(row['terms'])==expected for row in rows):
            raise ValueError('missing exact q*Dt=Dt1 row')
        pivot=highs[0]
        poly={():-1,(highden,):1,(pivot['slack'],):-1}
        for m in lows:poly[tuple(sorted((q,m['remainder'])))]=-1
        for m in highs:poly[(m['remainder'],)]=-1
        replacements[pivot['row']]=dict(label='pooled.weighted_low_digits',terms=contract.dump(poly))
        deleted_rows.add(lows[0]['row']);deleted_vars.add(lows[0]['slack'])
        weighted_cert=dict(q=q,lower_denominator=lowden,upper_denominator=highden,
                           lower_members=lows,upper_members=highs,pivot=pivot,
                           soundness='q*r_lower <= q*Dt-1 and r_upper <= Dt1-1')
    digit=None
    if drop_digit:
        did=[i for i,r in enumerate(rows) if r['label']=='choose0.digit_bound']
        if len(did)!=1:raise ValueError('no unique digit row')
        rid=did[0];slack=source_name['choose0.modular_oslack']
        digit=dict(row=rid,slack=slack,deleted_residual=rows[rid],
                   restoration='q - B - 1',justification='power bootstrap q >= B^4 > B >= 2')
        deleted_rows.add(rid);deleted_vars.add(slack)
    for v in deleted_vars:
        occurrences={i for i,r in enumerate(rows) if any(v in m for c,m in r['terms'])}
        if not occurrences<=deleted_rows:raise ValueError('deleted coordinate has another occurrence')
    retained=[i for i in range(len(variables)) if i not in deleted_vars]
    remap={v:i for i,v in enumerate(retained)}
    out=copy.deepcopy(source)
    out['variables']=[copy.deepcopy(variables[i]) for i in retained]
    for group_no,(_,members) in enumerate(sorted(groups.items())):
        if members[0]['slack'] in remap:
            out['variables'][remap[members[0]['slack']]]['name']='pooled.low_digits.'+str(group_no)+'.slack'
    out['residuals']=[]
    row_ids=[i for i in range(len(rows)) if i not in deleted_rows]
    if ordered:
        priority=json.loads((HERE/'source/row_priority.json').read_text())
        if sorted(priority)!=list(range(len(rows))):raise ValueError('bad row permutation')
        row_ids.sort(key=lambda i:priority[i])
    for i in row_ids:
        row=rows[i]
        if i in deleted_rows:continue
        r=replacements.get(i,row)
        out['residuals'].append(dict(label=r['label'],terms=[[c,[remap[v] for v in m]]for c,m in r['terms']]))
    out['variant']='cofinal-anchor-pooled-digits'+('-derived-output-bound' if drop_digit else '')
    out['metrics']={'variables':len(retained),'quadratic_rows':len(out['residuals']),
                    'exact_degree':4,'source_variables':len(variables),'source_rows':len(rows)}
    certificate=dict(schema='cofinal-pooled-transform/v1',source_sha256=hashlib.sha256(contract.canonical(source)).hexdigest(),
        target_sha256=hashlib.sha256(contract.canonical(out)).hexdigest(),groups=cert,
        digit_bound=digit,removed_rows=sorted(deleted_rows),removed_variables=sorted(deleted_vars),retained_original_indices=retained,
        retained_original_row_indices=row_ids,weighted=weighted_cert)
    return out,certificate

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--support-cap',type=int,default=48);p.add_argument('--keep-digit-bound',action='store_true');p.add_argument('--source-priority',action='store_true');p.add_argument('--weighted',action='store_true')
    args=p.parse_args()
    source=json.loads((HERE/'source/equation.json').read_text())
    raw,trans=transform(source,not args.keep_digit_bound,args.source_priority,args.weighted)
    target,cert,polynomial=contract.contract(raw,support_cap=args.support_cap)
    receipt,independent=check.verify(raw,target,cert)
    if polynomial['terms']!=independent:raise ValueError('independent expansion mismatch')
    for name,obj in [('raw_equation.json',raw),('transformation.json',trans),('equation.json',target),
                     ('projection.json',cert),('expanded_polynomial.json',polynomial),('metrics.json',receipt)]:write(args.output/name,obj)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
