#!/usr/bin/env python3
"""Check every path/branch uniformly over all valid register files.

The imported symbolic executor leaves the entire register file as a box.
Its four universal box laws are documented and proved in vendor/.../Box.v;
the only modified surviving transition (old state 3 reading 0) is outside
those excursions. Exact gaps 37, 38, 39 and the affine gap 40+n, n>=0,
cover every gap at least 37. This Python replay is not a Coq kernel run.
"""
from pathlib import Path
import json
import macro252 as M

def verify():
    out={}
    for gap,exact in [(37,True),(38,True),(39,True),(40,False)]:
        ns=M.m.executor();failures=[];count=0
        for p,(op,r) in M.OPS.items():
            for br in ('z','p') if op=='CD' else ('-',):
                count+=1
                got=M.m.case(ns,p,op,r,br,gap,exact_gap=exact)
                if not got[0]:failures.append({'path':p,'op':op,'r':r,'branch':br,'result':got})
        assert count==8391
        assert not failures,(gap,failures)
        out[str(gap)]={'exact_gap':exact,'cases':count,'failures':failures}
    return out

if __name__=='__main__':
    out=verify()
    p=Path(__file__).resolve().parents[1]/'certificates/uniform252.json'
    p.write_text(json.dumps(out,indent=2)+'\n')
    print('Uniform runtime checks: 4 x 8391 passed, all gaps >= 37.')
