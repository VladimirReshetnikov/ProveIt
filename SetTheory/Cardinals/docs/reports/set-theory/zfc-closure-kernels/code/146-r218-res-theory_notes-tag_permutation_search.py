#!/usr/bin/env python3
"""Screen all I/Q/E tag permutations fixing R=1 and native falsum=1.

Every constructor invocation is independently bound to a literal closed
27-leaf 4*Cantor core and 0..3 increments. Both GEN and MP are included.
Edits retain all arithmetic cores and change only their completed output.
"""
from pathlib import Path
import itertools
import json
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import signature_search as sig

a,z,s=sig.a,sig.z,sig.s
ROOT=Path(__file__).resolve().parents[1]
OLD_TAG={119:0,181:1,180:2,182:3}
TAG_MACRO={0:119,1:181,2:180,3:182}
inc=('CI',1)


def expanded(word):
    result=[]
    for m in word:
        result.extend({218:[177,119],183:[177,119,180,177,119]}.get(m,[m]))
    return result


def calls():
    result=[]
    for name,word in sig.words.items():
        start=sig.intervals[name][0]
        for m in expanded(word):
            end=start+len(z.flat(z.MACRO[m]))
            if m in OLD_TAG:result.append((name,m,start,end))
            start=end
        assert start==sig.intervals[name][1]
    extra=[('rho8',194,221),('rho8',247,274),('rho8',326,353),
           ('rho8',405,432),('rho8',432,459),('rho8',459,486),
           ('GEN',92,121),('MP',4678,4705)]
    for name,lo,hi in extra:
        m=180 if name=='GEN' else 119
        assert z.flat(a.old)[lo:hi]==z.flat(z.MACRO[m])
        result.append((name,m,lo,hi))
    result.sort(key=lambda t:t[2])
    for name,m,lo,hi in result:
        core=a.chunks(a.old,lo,lo+27)
        assert len(core)==1 and core[0][2]==z.MACRO[119]
        assert z.flat(a.old)[lo+27:hi]==(inc,)*OLD_TAG[m]
    return result


CALLS=calls()


def swap_input_registers(t):
    if s.leaf(t):
        op,r=t
        return (op,{1:6,6:1}.get(r,r)) if op in('CI','CD') else t
    return swap_input_registers(t[0]),swap_input_registers(t[1])


CORE=z.MACRO[119]
assert len(z.flat(CORE[0]))==11 and len(z.flat(CORE[1][0]))==10
assert len(z.flat(CORE[1][1]))==6
assert s.boundary(CORE[1][0])==(0,0,False)
REVERSED_CORE=CORE[0],(swap_input_registers(CORE[1][0]),CORE[1][1])
assert s.boundary(REVERSED_CORE)==(0,0,False)


def constructor_core(multiplier=4,reversed=False):
    assert multiplier in(2,4,8)
    block=inc
    for _ in range(multiplier.bit_length()-1):block=block,block
    multiply=('CD',7),(block,('CC',2))
    pair=swap_input_registers(CORE[1][0])if reversed else CORE[1][0]
    core=CORE[0],(pair,multiply)
    assert s.boundary(core)==(0,0,False)
    return core


assert constructor_core()==CORE
assert constructor_core(reversed=True)==REVERSED_CORE


def edit(tags,add_policy=0,delete_policy=0,inc_shape=0,reverse=(),multipliers=None):
    replacements={}
    deletions=set()
    intervals=[]
    multipliers=multipliers or {}
    def incs(n):
        assert n>0
        t=inc
        for _ in range(n-1):t=(t,inc)if inc_shape==0 else (inc,t)
        return t
    for name,m,lo,hi in CALLS:
        old=OLD_TAG[m];new=tags[m];delta=new-old
        multiplier=multipliers.get(m,4)
        core=constructor_core(multiplier,m in reverse)
        if core!=CORE:replacements[lo,lo+27]=core
        if delta>0:
            if old==0:
                # The exact old whole arithmetic core is a closed subtree.
                replacements[lo,lo+27]=(core,incs(delta))
            elif add_policy==0:
                replacements[lo,lo+27]=(core,incs(delta))
            elif add_policy==1:
                replacements[lo+27,lo+28]=incs(delta+1)
            else:
                replacements[hi-1,hi]=incs(delta+1)
        elif delta<0:
            locations=list(range(lo+27,hi))
            if delete_policy==1:locations.reverse()
            if delete_policy==2:locations.sort(key=lambda i:(abs(2*i-(lo+27+hi-1)),i))
            deletions.update(locations[:-delta])
        intervals.append(dict(role=name,old_macro=m,old_tag=old,new_tag=new,new_multiplier=multiplier,reversed_pairing=m in reverse,interval=[lo,hi]))
    touched=[]
    def go(t,start=0):
        end=start+len(z.flat(t))
        if (start,end)in replacements:
            assert s.boundary(t)==(0,0,False)
            touched.append((start,end));return replacements[start,end]
        if s.leaf(t):
            if start in deletions:
                assert t==inc
                return None
            return t
        l=go(t[0],start)
        r=go(t[1],start+len(z.flat(t[0])))
        return r if l is None else l if r is None else (l,r)
    tree=go(a.old)
    assert set(touched)==set(replacements)
    # Verify the exact full primitive word, independently by disjoint interval
    # reconstruction from old cores and new constant increments.
    expected=[];end=0;flat=z.flat(a.old)
    for _,m,lo,hi in CALLS:
        expected.extend(flat[end:lo]);expected.extend(z.flat(constructor_core(multipliers.get(m,4),m in reverse)));expected.extend([inc]*tags[m]);end=hi
    expected.extend(flat[end:])
    assert z.flat(tree)==tuple(expected)
    rr=s.sites(tree)
    assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
    return tree,intervals


def main():
    out=ROOT/'theory_notes/tag_variants';out.mkdir(exist_ok=True)
    objective=a.hw.make(a.table,a.old)[0]
    results=[];best=999;start=time.monotonic();seen=set()
    for values in itertools.permutations((0,2,3)):
        tags=dict(zip((119,180,182),values));tags[181]=1
        local=[]
        for ap,dp,shape in itertools.product(range(3),range(3),range(2)):
            tree,binding=edit(tags,ap,dp,shape)
            if tree in seen:continue
            seen.add(tree)
            score=objective(tree)
            row=dict(tags=dict(zip(('I','Q','E'),values)),addition_policy=ap,deletion_policy=dp,increment_shape=shape,hardware_lower_bound=score,metrics=s.metrics(tree))
            results.append(row);local.append(row)
            if score['cost_lower_bound']<best:
                best=score['cost_lower_bound'];print('BEST',json.dumps(row),flush=True)
            if score['cost_lower_bound']<=221:
                d=out/('t'+''.join(map(str,values))+f'_a{ap}_d{dp}_s{shape}');d.mkdir(exist_ok=True)
                (d/'sites.json').write_bytes(s.compact(s.sites(tree)))
                (d/'receipt.json').write_text(json.dumps(dict(**row,constructor_bindings=binding),indent=2)+'\n')
        if local:print('TAGS',values,'distinct',len(local),'best',min(r['hardware_lower_bound']['cost_lower_bound']for r in local),'seconds',time.monotonic()-start,flush=True)
    (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    (out/'constructor_bindings.json').write_text(json.dumps(CALLS,indent=2)+'\n')
    print('DONE',len(results),'best',best,'seconds',time.monotonic()-start,flush=True)


if __name__=='__main__':main()
