#!/usr/bin/env python3
"""Verify the two194-state research compositions, without a new-state claim."""
from pathlib import Path
import argparse,hashlib,importlib.util,json

HERE=Path(__file__).resolve().parent

def read_table(path):
    rows={}
    for ln in path.read_text().splitlines():
        q,b,w,d,n=ln.split();key=int(q),int(b)
        if key in rows or d not in ('L','R'):raise ValueError(ln)
        rows[key]=int(w),d=='R',int(n)
    return rows

def verify(reference_root):
    runtime=reference_root/'reference/haz/vendor/symbolic_runtime.py'
    spec=importlib.util.spec_from_file_location('companion_runtime',runtime)
    c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
    primary=read_table(reference_root/'reference/haz/inputs/pa194.native.tm')
    c.PHYSICAL[:]=[6,2,0,3,4,7,8,5,1]
    results=[]
    for family in ['PA194R_AD','PA194F_AD']:
        src=HERE/'companions'/family
        rows=read_table(src/'machine.native.tm')
        expected=json.loads((src/'receipt.json').read_text())
        assert len(rows)==388
        assert hashlib.sha256((src/'machine.native.tm').read_bytes()).hexdigest()==expected['native_sha256']
        assert all(rows[q,b]==primary[q,b] for q in c.BOXSTATES for b in (0,1))
        sites=json.loads((src/'sites.json').read_text());ins=json.loads((src/'instructions.json').read_text())
        def frame(i,extra=0,effect=c.PLAIN):return c.frame(tuple(map(int,sites[i][0])),extra,effect)
        def target(i,extra=0,effect=c.PLAIN):return c.canonical(frame(i,extra,effect))
        contracts=[]
        for i,code in enumerate(ins):
            st=frame(i)
            if code[0]=='inc':
                _,r,n=code;contracts.append((i,None,st,target(n,0,('x','inc',c.PHYSICAL[r]))))
            elif code[0]=='dec':
                _,r,z,p=code
                contracts.append((i,(c.PHYSICAL[r],True),st,target(z)))
                contracts.append((i,(c.PHYSICAL[r],False),st,target(p,1,('x','dec',c.PHYSICAL[r]))))
            elif code[0]=='jump':contracts.append((i,None,st,target(code[1])))
            else:contracts.append((i,None,st,None))
        actual=c.validate(rows,contracts)
        assert actual==expected['source_contracts'],(family,actual)
        h0=-2;ones_expected={h0-1,h0+48}
        ones_expected.update(h0+i for i,b in enumerate(sites[25][0]) if b=='1')
        position=h0+48
        for value in [0,0,0,0,0,0,2,0,0]+[1]*26:
            position+=2;ones_expected.update(range(position,position+value+1));position+=value
        q=74;h=0;ones=set();steps=None
        for tick in range(1,1000001):
            w,d,q=rows[q,int(h in ones)]
            (ones.add if w else ones.discard)(h);h+=1 if d else -1
            assert q!=254,('early halt',family,tick)
            if (q,h,ones)==(84,h0,ones_expected):steps=tick;break
        assert steps==expected['complete_blank_seed_steps']==57736
        results.append({'family':family,'states':194,'source_outcomes':actual,
                        'complete_blank_seed_steps':steps,'arithmetic_box_rows_unchanged':True,
                        'status':'Verified inherited runtime contracts; not a sub194 result'})
    return results

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--reference-root',required=True,type=Path)
    args=ap.parse_args();print(json.dumps(verify(args.reference_root.resolve()),indent=2))
