#!/usr/bin/env python3
"""Independent complete raw natural pooling reconstruction, no producer import."""
import copy
import hashlib
import json
from collections import Counter
from pathlib import Path
from check_signed_transform import plus, times, scaled, v, row_named, fingerprint, require

ROOT=Path(__file__).resolve().parents[1]
RELEASE=ROOT/'natural'
PRIOR=ROOT/'prior_direct_closure/architecture/strict_natural229/raw/equation.json'
SMALL=['choose0','crt.range.index']
BIG=['crt.range.'+s for s in ['a','b','c','d','derived_label_sum']]
GROUPS=[('t0','pow3.output',SMALL),('t','mul.422',BIG),('y','pow4.output',['crt.range.S','crt.range.Sp']),('x','pow5.output',['crt.range.u','crt.range.vq'])]

def checked(endpoint,supplied=None):
    old=json.loads((RELEASE/'source/equation.json').read_text())
    require(old==json.loads(PRIOR.read_text()),'parent literal binding')
    names=[r['name'] for r in old['variables']]
    require(len(set(names))==len(names),'duplicate original names')
    bylabel={r['label']:row_named(r,names) for r in old['residuals'] if r['label'].endswith('.remainder_bound') or r['label']=='choose0.digit_bound'}
    removed=set()
    for _,d,requests in GROUPS:
        for req in requests:
            label=req+'.remainder_bound'
            require(bylabel[label]==plus(v(d),scaled(v(req+'.modular_remainder'),-1),scaled(v(req+'.modular_rslack'),-1),{():-1}),('original bound shape',label))
            removed.add(label)
    require(bylabel['choose0.digit_bound']==plus(v('pow2.output'),scaled(v('choose0.output'),-1),scaled(v('choose0.modular_oslack'),-1),{():-1}),'original output bound shape')
    strategy=endpoint['strategy']
    require(strategy in ['four','three_with_digit'],'unsupported strategy')
    groups=GROUPS if strategy=='four' else [('t','mul.422',SMALL+BIG)]+GROUPS[2:]
    if strategy=='three_with_digit':removed.add('choose0.digit_bound')
    renames={reqs[0]+'.modular_rslack':'pooled_digits.'+label+'.slack' for label,_,reqs in groups}
    def rename(p):return {tuple(sorted(renames.get(n,n) for n in mon)):c for mon,c in p.items()}
    expected=[(r['label'],rename(row_named(r,names))) for r in old['residuals'] if r['label'] not in removed]
    for label,d,requests in groups:
        p=plus(v(d),scaled(v('pooled_digits.'+label+'.slack'),-1),{():-1})
        for req in requests:
            term=v(req+'.modular_remainder')
            if strategy!='four' and req in SMALL:term=times(v('pow2.output'),term)
            p=plus(p,scaled(term,-1))
        if strategy=='three_with_digit' and label=='t':p=plus(p,scaled(times(v('choose0.output'),v('pow3.output')),-1))
        expected.append(('pooled_digits.'+label,p))
    path=RELEASE/'endpoints'/endpoint['name']/'source/equation.json'
    new=supplied or json.loads(path.read_text())
    nn=[z['name'] for z in new['variables']]
    require(len(set(nn))==len(nn),'duplicate output names')
    got=Counter((r['label'],fingerprint(row_named(r,nn))) for r in new['residuals'])
    want=Counter((label,fingerprint(p)) for label,p in expected)
    require(got==want,'complete residual multiset mismatch')
    require(set(nn)=={n for _,p in expected for mon in p for n in mon},'variable support mismatch')
    require(all(len(mon)<=2 for _,p in expected for mon in p),'degree exceeds two')
    order=json.loads((path.parent/'row_order.json').read_text())
    require(sorted(order)==list(range(len(expected))),'row order is not a permutation')
    return {'endpoint':endpoint['name'],'strategy':strategy,'raw_variables':len(nn),'raw_rows':len(new['residuals']),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def main():
    records=[];controls=0
    for ep in json.loads((RELEASE/'ENDPOINTS.json').read_text()):
        records.append(checked(ep))
        original=json.loads((RELEASE/'endpoints'/ep['name']/'source/equation.json').read_text())
        for row in original['residuals']:
            if not row['label'].startswith('pooled_digits.'):continue
            bad=copy.deepcopy(original)
            next(r for r in bad['residuals'] if r['label']==row['label'])['terms'][0][0]+=1
            try:checked(ep,bad)
            except ValueError:controls+=1
            else:raise ValueError('mutation accepted')
    print(json.dumps({'status':'PASS','scope':'exact complete raw pooling replacement, inherited binding, original bound recognition, all unchanged rows, variable names/support, degree and row permutation','endpoints':records,'mutated_pool_rows_rejected':controls},indent=2))

if __name__=='__main__':main()
