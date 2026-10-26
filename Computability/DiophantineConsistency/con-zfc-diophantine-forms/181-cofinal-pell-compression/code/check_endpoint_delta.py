#!/usr/bin/env python3
"""Independent literal audit of the two one-square quartic endpoints.

This file imports no code from the producer or its inherited algebra helpers.
It checks all residuals using inherited variable names, expands every square
by direct integer convolution, and verifies the global polynomial identity

    P_new = P_parent[v := u] - 2 F + 1,

where F is the parent's final frame residual (after v := u). The identity is
an artifact check; the new zero-existence theorem additionally uses the
ordinary cofinal Pell proof and the inherited semantic calibration.
"""
import argparse
import copy
import hashlib
import json
from collections import defaultdict
from pathlib import Path


def require(test,message):
    if not test:
        raise ValueError(message)


def terms_to_dict(terms,nvars,label):
    out={}
    for item in terms:
        require(isinstance(item,list) and len(item)==2,label+': malformed term')
        coeff,mon=item
        require(type(coeff) is int and coeff!=0,label+': coefficient is not a nonzero integer')
        require(isinstance(mon,list) and all(type(i) is int and 0<=i<nvars for i in mon),
                label+': invalid monomial coordinate')
        require(mon==sorted(mon),label+': unsorted monomial')
        key=tuple(mon)
        require(key not in out,label+': duplicate monomial')
        out[key]=coeff
    return out


def equation_rows(eq,label):
    require(eq['domain']=='unrestricted integers',label+': wrong domain')
    names=[v['name'] for v in eq['variables']]
    require(len(names)==len(set(names)),label+': duplicate variable name')
    rows=[terms_to_dict(row['terms'],len(names),label+f' row {i}')
          for i,row in enumerate(eq['residuals'])]
    require(all(len(m)<=2 for row in rows for m in row),label+': nonquadratic residual')
    require(set(range(len(names)))=={i for row in rows for m in row for i in m},
            label+': unused or missing coordinate')
    return names,rows


def rename(poly,mapping):
    out=defaultdict(int)
    for mon,c in poly.items():
        out[tuple(sorted(mapping[i] for i in mon))]+=c
    return {m:c for m,c in out.items() if c}


def add(poly,delta):
    out=dict(poly)
    for mon,c in delta.items():
        out[mon]=out.get(mon,0)+c
        if out[mon]==0:
            del out[mon]
    return out


def sum_of_squares(rows):
    out=defaultdict(int)
    for row in rows:
        for m,c in row.items():
            for n,d in row.items():
                out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}


def metrics(names,rows,expanded):
    return dict(variables=len(names),residuals=len(rows),
                residual_monomials=sum(len(row) for row in rows),
                residual_height=max(abs(c) for row in rows for c in row.values()),
                degree=max(map(len,expanded)),monomials=len(expanded),
                height=max(map(abs,expanded.values())))


def audit(parent,new,expanded_doc,metrics_doc,label):
    old_names,old_rows=equation_rows(parent,label+' parent')
    names,rows=equation_rows(new,label+' new')
    require('free_A.v' in old_names and 'free_A.u' in old_names,'missing parent center variables')
    require('free_A.v' not in names and 'free_A.u' in names,'new center coordinates wrong')
    iv=old_names.index('free_A.v')
    iu=old_names.index('free_A.u')
    require([v for i,v in enumerate(parent['variables']) if i!=iv]==new['variables'],
            label+': metadata/order differ beyond removal of private v')
    by_name={name:i for i,name in enumerate(names)}
    mapping={i:by_name['free_A.u' if name=='free_A.v' else name]
             for i,name in enumerate(old_names)}
    labels=[r['label'] for r in parent['residuals']]
    require(labels==[r['label'] for r in new['residuals']],label+': row labels changed')
    require(labels.count('shared.frame_definition')==1,label+': ambiguous frame')
    require(labels.count('free_A.cofinal_constructor')==1,label+': ambiguous center')
    fi=labels.index('shared.frame_definition')
    ci=labels.index('free_A.cofinal_constructor')
    require(old_rows[ci].get((iv,iv))==-1 and old_rows[ci].get((iu,iu))==-1,
            label+': parent center has wrong square coefficients')
    require(all(iv not in mon for j,row in enumerate(old_rows) if j!=ci for mon in row),
            label+': removed v is not private')
    require(sum(iv in mon for mon in old_rows[ci])==1,label+': v has extra center occurrence')
    reduced=[rename(row,mapping) for row in old_rows]
    for j,(expect,actual) in enumerate(zip(reduced,rows)):
        if j==fi:
            expect=add(expect,{():-1})
        require(expect==actual,label+f': unexpected endpoint delta in row {j}')
    expanded=sum_of_squares(rows)
    stored=terms_to_dict(expanded_doc['terms'],len(names),label+' expanded polynomial')
    require(expanded_doc['variables']==len(names),label+': expansion dimension wrong')
    require(stored==expanded,label+': stored collected polynomial differs')
    # Check the same result globally, by expanding the original parent first.
    parent_expanded=sum_of_squares(old_rows)
    restricted_parent=rename(parent_expanded,mapping)
    correction={m:-2*c for m,c in reduced[fi].items()}
    correction=add(correction,{():1})
    require(add(restricted_parent,correction)==expanded,
            label+': P_new = P_parent[v=u]-2F+1 failed')
    new_metrics=metrics(names,rows,expanded)
    require(new_metrics==metrics_doc,label+': claimed metrics differ')
    return {'parent':metrics(old_names,old_rows,parent_expanded),
            'new':new_metrics,'frame_row':fi,'center_row':ci,
            'removed_parent_coordinate':iv,
            'identified_parent_coordinate':iu,
            'all_other_residuals':'exact after variable identification',
            'global_identity':'P_new = P_parent[v=u] - 2F + 1'}


def expect_rejection(function,description):
    try:
        function()
    except ValueError:
        return description
    raise ValueError('corruption was accepted: '+description)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('package_root',nargs='?',type=Path,default=Path(__file__).resolve().parents[1])
    args=ap.parse_args()
    base=args.package_root
    receipt={'status':'passed','profiles':{},'negative_controls':[]}
    for label,n in [('balanced',229),('compact',228)]:
        oldfile=base/'inherited/package166/equations'/label/'equation.json'
        endpoint=base/f'equations/P{n}_{label}'
        newfile=endpoint/'equation.json'
        parent=json.loads(oldfile.read_text())
        new=json.loads(newfile.read_text())
        expanded=json.loads((endpoint/'expanded_polynomial.json').read_text())
        stated=json.loads((endpoint/'metrics.json').read_text())
        result=audit(parent,new,expanded,stated,label)
        result['parent_sha256']=hashlib.sha256(oldfile.read_bytes()).hexdigest()
        result['new_sha256']=hashlib.sha256(newfile.read_bytes()).hexdigest()
        receipt['profiles'][label]=result
        wrong=copy.deepcopy(new)
        wrong['residuals'][result['frame_row']]['terms'][0][0]+=1
        receipt['negative_controls'].append(expect_rejection(
            lambda:audit(parent,wrong,expanded,stated,label),label+': changed frame coefficient'))
        wrong_exp=copy.deepcopy(expanded)
        wrong_exp['terms'][0][0]+=1
        receipt['negative_controls'].append(expect_rejection(
            lambda:audit(parent,new,wrong_exp,stated,label),label+': changed collected coefficient'))
        wrong_center=copy.deepcopy(new)
        idx=next(i for i,v in enumerate(new['variables']) if v['name']=='free_A.u')
        ts=wrong_center['residuals'][result['center_row']]['terms']
        term=next(t for t in ts if t[1]==[idx,idx])
        term[0]=-1
        receipt['negative_controls'].append(expect_rejection(
            lambda:audit(parent,wrong_center,expanded,stated,label),label+': removed scale-two coefficient'))
    receipt['scope']='Independent finite identities and exact integer expansion; unbounded semantic equivalence is proved separately.'
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
