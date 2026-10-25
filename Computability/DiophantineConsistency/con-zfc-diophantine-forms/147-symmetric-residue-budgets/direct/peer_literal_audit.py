#!/usr/bin/env python3
"""Independent review: changed source rows and final sum-of-squares lists.

Reads JSON as data and imports no producer, projector, or parent code.
"""
from collections import defaultdict
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent


def require(ok,message):
    if not ok:
        raise ValueError(message)


def polynomial(terms):
    out=defaultdict(int)
    for coefficient,monomial in terms:
        out[tuple(sorted(monomial))]+=coefficient
    return {m:c for m,c in out.items() if c}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_source(dirname,merged,odd):
    old=json.loads((ROOT/'inherited/guarded.json').read_text())
    new=json.loads((ROOT/dirname/'source.json').read_text())
    names={v['name']:j for j,v in enumerate(new['variables'])}
    require(new['variables'][:len(old['variables'])]==old['variables'], 'Old variable prefix differs')
    removed={f'domain_guard.{j}' for j in range(3,14)}
    if odd: removed.add('domain_guard.2')
    expected_prefix=[r for r in old['residuals'] if r['label'] not in removed]
    require(new['residuals'][:len(expected_prefix)]==expected_prefix, 'Unrelated old residual changed')
    require(len(old['residuals'])-len(expected_prefix)==11+int(odd), 'Deletion count differs')
    extra=new['residuals'][len(expected_prefix):]
    actual={r['label']:polynomial(r['terms']) for r in extra}
    require(len(actual)==len(extra), 'Duplicate new row label')
    groups=[('t','pow4.output',['choose0.remainder','range8.remainder']),
            ('tplus1','pow6.output',[f'range{j}.remainder' for j in (0,1,2,3,9)]),
            ('yplus1','pow11.output',[f'range{j}.remainder' for j in (4,5)]),
            ('x','pow14.output',[f'range{j}.remainder' for j in (6,7)])]
    expected={}
    if odd:
        z=names['odd_radix.root'];q=names['pow2.output']
        expected['odd_radix.square']={(q,):1,(z,z):-4,(z,):-4,():-1}
    if merged:
        scaled=[]
        for name in groups[0][2]:
            scaled_name='digit_pool.scaled.'+name
            z,r,q=names[scaled_name],names[name],names['pow2.output']
            expected['digit_pool.scale.'+name]={(z,):1,tuple(sorted((q,r))):-1}
            scaled.append(scaled_name)
        groups=[('t_and_tplus1',groups[1][1],groups[1][2]+scaled)]+groups[2:]
    for tag,Dname,rems in groups:
        D=names[Dname]
        p={(D,D):1,():-1}
        for name in rems:
            r=names[name];p[r,r]=-4
        for name in ('a','b','c'):
            a=names[f'digit_pool.{tag}.{name}'];p[a,a]=-1
            if name=='c':p[a,]=-1
        expected['digit_pool.'+tag]=p
    require(actual==expected,'New rows do not match reviewed formulas')
    return {'source_sha256':digest(ROOT/dirname/'source.json'),
            'unchanged_residuals':len(expected_prefix),
            'deleted_sign_rows':len(removed),'new_rows':len(extra),
            'all_new_rows_exact':True}


def check_sos(dirname):
    folder=ROOT/dirname
    data=json.loads((folder/'equation.json').read_text())
    expanded=json.loads((folder/'expanded_polynomial.json').read_text())
    out=defaultdict(int)
    for row in data['residuals']:
        p=polynomial(row['terms'])
        require(max(map(len,p),default=0)<=2,'Nonquadratic row')
        for m,c in p.items():
            for n,d in p.items():
                out[tuple(sorted(m+n))]+=c*d
    out={m:c for m,c in out.items() if c}
    require(out==polynomial(expanded['terms']),'Sum of squares differs from literal expanded coefficients')
    used={i for m in out for i in m}
    require(used==set(range(len(data['variables']))),'Unused or undeclared coordinate')
    metrics={'variables':len(data['variables']), 'rows':len(data['residuals']),
             'degree':max(map(len,out)), 'monomials':len(out),
             'height':max(map(abs,out.values()))}
    stated=json.loads((folder/'METRICS.json').read_text())
    require(all(stated[k]==v for k,v in metrics.items()),'Claimed metric differs')
    metrics.update(equation_sha256=digest(folder/'equation.json'),
                   expanded_sha256=digest(folder/'expanded_polynomial.json'),
                   independent_full_SOS_expansion=True)
    return metrics


def main():
    result={'scope':'Independent exact new-row census and full final SOS expansion; imports no producer/projector code.',
            'proof_sha256':digest(ROOT/'PROOF.md'),'source_deltas':{},'endpoints':{}}
    for name,merged,odd in [('four_pools',False,False),('three_pools',True,False),('odd_three_pools',True,True)]:
        result['source_deltas'][name]=check_source(name,merged,odd)
        result['endpoints'][name+'_centered']=check_sos(name+'_centered')
    result['status']='PASS'
    text=json.dumps(result,indent=2)+'\n'
    (ROOT/'INDEPENDENT_LITERAL_REVIEW.json').write_text(text)
    print(text,end='')


if __name__=='__main__':main()
