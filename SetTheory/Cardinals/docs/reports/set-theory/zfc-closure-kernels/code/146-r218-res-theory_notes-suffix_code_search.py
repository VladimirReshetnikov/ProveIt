#!/usr/bin/env python3
"""All 30 four-leaf binary suffix codes with R(0,0)=1.

Code_X(a,b) = 2**length_X * P(a,b) + tag_X. Prefix-free words read
least-significant-bit first are disjoint exhaustive residue classes. The
zero tag is assigned to I,Q,orE, whose all-zero formula is a tautology.
"""
from functools import lru_cache
from pathlib import Path
import itertools
import json
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import tag_permutation_search as t
from pair_orientation_search import run


@lru_cache(None)
def shapes(n):
    if n==1:return (None,)
    return tuple((l,r)for k in range(1,n)for l in shapes(k)for r in shapes(n-k))


def leaf_codes(shape,tag=0,length=0):
    if shape is None:return [(tag,length)]
    return leaf_codes(shape[0],tag,length+1)+leaf_codes(shape[1],tag+(1<<length),length+1)


def coding_families():
    result=[]
    for shape in shapes(4):
        codes=leaf_codes(shape)
        rel=[c for c in codes if c[0]==1]
        assert len(rel)==1
        other=[c for c in codes if c!=rel[0]]
        for perm in itertools.permutations(other):
            d=dict(zip((119,180,182),perm));d[181]=rel[0]
            result.append(d)
    assert len(result)==30
    return result


def check_code(d):
    # Exact finite residue partition suffices for every natural number: each
    # membership test depends only on the residue modulo the largest modulus.
    maximum=max(1<<length for tag,length in d.values())
    residue_owner=[]
    for n in range(maximum):
        owners=[m for m,(tag,length)in d.items()if n%(1<<length)==tag]
        assert len(owners)==1
        residue_owner.append(owners[0])
    assert d[181][0]==1
    assert residue_owner[0]!=181
    # Supplementary all-register local macro tests, including arbitrary stack
    # tails and unaffected registers. Mathematical induction is inherited
    # for pop/pair and trivial for multiplication by the positive constant.
    P=lambda a,b:(a+b)*(a+b+1)//2+b
    tests=0
    for m,(tag,length)in d.items():
        mult=1<<length
        core=t.constructor_core(mult)
        for x,y,tail in itertools.product(range(3),repeat=3):
            reg=[11,y,P(x,tail),13,17,19,0,0,23]
            expected=reg.copy();expected[1]=mult*P(x,y);expected[2]=tail
            assert run(core,reg,[1000000])==('N',0)and reg==expected
            tests+=1
    return dict(residue_modulus=maximum,residue_owner=residue_owner,
                exact_residue_partition=True,native_falsum_code=1,
                zero_constructor=residue_owner[0],finite_core_tests=tests)


def main():
    out=t.ROOT/'theory_notes/suffix_variants';out.mkdir(exist_ok=True)
    objective=t.a.hw.make(t.a.table,t.a.old)[0]
    results=[];best=999;start=time.monotonic();seen=set();family_results=[]
    names={119:'I',180:'Q',181:'R',182:'E'}
    for family,d in enumerate(coding_families()):
        tags={m:tag for m,(tag,length)in d.items()}
        factors={m:1<<length for m,(tag,length)in d.items()}
        code_audit=check_code(d)
        local=[]
        for add,delete,shape in itertools.product(range(3),range(3),range(2)):
            tree,binding=t.edit(tags,add,delete,shape,multipliers=factors)
            if tree in seen:continue
            seen.add(tree)
            score=objective(tree)
            row=dict(family=family,constructors={names[m]:dict(multiplier=factors[m],tag=tags[m])for m in names},addition_policy=add,deletion_policy=delete,increment_shape=shape,hardware_lower_bound=score,metrics=t.s.metrics(tree))
            results.append(row);local.append(row)
            if score['cost_lower_bound']<best:
                best=score['cost_lower_bound'];print('BEST',json.dumps(row),flush=True)
            if score['cost_lower_bound']<=221:
                path=out/f'f{family:02d}_a{add}_d{delete}_s{shape}';path.mkdir(exist_ok=True)
                (path/'sites.json').write_bytes(t.s.compact(t.s.sites(tree)))
                (path/'receipt.json').write_text(json.dumps(dict(**row,code_audit=code_audit,constructor_bindings=binding),indent=2)+'\n')
        entry=dict(family=family,code={names[m]:d[m]for m in names},code_audit=code_audit,
                   distinct_layouts=len(local),best_lower_bound=min(r['hardware_lower_bound']['cost_lower_bound']for r in local))
        family_results.append(entry)
        print('FAMILY',family,'code',entry['code'],'layouts',len(local),'best',entry['best_lower_bound'],'seconds',time.monotonic()-start,flush=True)
        (out/'family_results.json').write_text(json.dumps(family_results,indent=2)+'\n')
    (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('DONE',len(results),'best',best,'seconds',time.monotonic()-start,flush=True)


if __name__=='__main__':main()
