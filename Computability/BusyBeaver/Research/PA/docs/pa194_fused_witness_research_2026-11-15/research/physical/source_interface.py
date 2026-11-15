#!/usr/bin/env python3
"""Inspect literal/symbolic row coverage under the recorded source invariant."""
import sys,json
from pathlib import Path
import search_runtime as sr
HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
INPUT=HERE/'inputs'
sys.path.insert(0,str(VENDOR))
import symbolic_runtime as rt
sites=json.loads((INPUT/'pa194.sites.json').read_text())
ins=json.loads((INPUT/'pa194.instructions.json').read_text())
def makecontracts():
    def frame(i,extra=0,effect=rt.PLAIN):return rt.frame(tuple(map(int,sites[i][0])),extra,effect)
    def target(i,extra=0,effect=rt.PLAIN):return rt.canonical(frame(i,extra,effect))
    cs=[]
    for i,code in enumerate(ins):
        st=frame(i)
        if code[0]=='inc':_,r,n=code;cs.append((i,None,st,target(n,0,('x','inc',rt.PHYSICAL[r]))))
        elif code[0]=='dec':_,r,z,n=code;cs.extend([(i,(rt.PHYSICAL[r],True),st,target(z)),(i,(rt.PHYSICAL[r],False),st,target(n,1,('x','dec',rt.PHYSICAL[r])))])
        elif code[0]=='jump':cs.append((i,None,st,target(code[1])))
        else:cs.append((i,None,st,None))
    return cs
cs=makecontracts()
def collect(rows,restricted=False):
    covered=set()
    source={}
    def observe(s):
        q,onl,left,right=s
        segs=left if onl else right
        if not segs: b=0
        elif segs[0][0]=='b':b=segs[0][1]
        elif segs[0][0]=='r':b=segs[0][1]
        else:return
        covered.add((q,b))
    for c in cs:
        i,br=c[:2]
        if restricted and (i in [8,3635,3636] or (i in [7,3634] and br and not br[1])):continue
        n=rt.run(rows,c,observe=observe)
        assert n is not None,(i,br)
    return covered
