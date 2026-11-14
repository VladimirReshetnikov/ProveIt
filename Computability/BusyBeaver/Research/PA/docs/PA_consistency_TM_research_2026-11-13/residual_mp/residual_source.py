#!/usr/bin/env python3
"""Construct a parameter-free MP variant of the exact PA196 source.

The inherited source-splice utilities are used only as untrusted syntax tools.
Two independent ordinal CFG resolvers and isolated comparison checks run here.
This file does not certify a physical machine or a PA consistency theorem.
"""
from pathlib import Path
import sys,json,hashlib,argparse
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Verification requires assertions; run Python without -O or -OO.')
HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
BASE=HERE/'inputs'
sys.path.insert(0,str(VENDOR))
import source_language as s
import source_splice as sp

def run(gate,regs,limit=100000):
    rows=s.sites((gate,('CH',None)));g=sp.cfg_intervals(rows)
    assert g==sp.cfg_arithmetic(rows)
    pc=0;regs=list(regs)
    for steps in range(limit):
        op,r,to=g[pc]
        if op=='CH':return regs,steps
        if op=='CI':regs[r]+=1;pc=to[0]
        elif op=='CD':
            positive=int(regs[r]>0);regs[r]-=positive;pc=to[positive]
        else:pc=to[0]
    raise ValueError('finite probe bound')

def construct(output):
    raw=(BASE/'original.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='7204b25d70f0bc6fbc5fbb19d0ccdcb3fa88f9d63fa3610ca0b1c950617d34f9'
    rows=json.loads(raw);old=s.tree(rows)
    oldg=sp.cfg_intervals(rows);assert oldg==sp.cfg_arithmetic(rows)
    gate=sp.serial(sp.closed_forest(old,3680,3692))
    assert s.subtree(gate,'0110')==(('CD',6),('CC',2))
    newgate=s.replace(gate,'0110',(('CD',6),(('CI',4),('CC',2))))
    edits={(3680,3692):newgate,(3693,3707):None}
    new=sp.apply_closed_splices(old,edits);rr=s.sites(new);g=sp.cfg_intervals(rr)
    assert g==sp.cfg_arithmetic(rr)==[(o,r if o in ('CI','CD') else None,tuple(to)) for (o,r,to) in g]
    assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
    mapping={};replacement={};cursor=0
    for i in range(len(rows)):
        covered=next(((lo,hi,v)for(lo,hi),v in edits.items()if lo<=i<hi),None)
        if covered:
            lo,hi,v=covered
            if i==lo:replacement[lo]=(cursor,0 if v is None else sp.size(v));cursor+=0 if v is None else sp.size(v)
        else:mapping[i]=cursor;cursor+=1
    assert cursor==len(rr)
    def redirect(target):
        if target in mapping:return mapping[target]
        for(lo,hi),v in edits.items():
            if lo<=target<hi:
                assert target==lo,('outside entry into macro interior',target,lo,hi)
                return replacement[lo][0]if v is not None else redirect(hi%len(rows))
        raise ValueError(target)
    edges=0
    for i,j in mapping.items():
        op,r,to=oldg[i]
        assert g[j]==(op,r,tuple(redirect(t) for t in to)),(i,j,g[j],(op,r,to))
        assert rr[j][1:]==rows[i][1:];edges+=len(to)
    cases=0
    for D in range(64):
        for c in range(64):
            initial=[2,17,3,0,0,D,c,0,6];got,steps=run(newgate,initial)
            old_result,old_steps=run(gate,initial)
            expected=initial[:];expected[1]=0 if D==c else 17
            expected[4]=max(c-D-1,0);expected[5]=expected[6]=0
            assert got==expected,(D,c,got,expected);cases+=1
            expected_steps=3*D+2*17+3 if D==c else 3*c+2 if D<c else 2*D+c+4
            assert steps==expected_steps,(D,c,steps,expected_steps)
            assert old_steps==steps,(D,c,old_steps,steps)
            expected_old=expected[:];expected_old[4]=0
            assert old_result==expected_old,(D,c,old_result,expected_old)
    output.mkdir(parents=True,exist_ok=True)
    encoded=s.compact(rr);(output/'sites.json').write_bytes(encoded)
    result={'baseline_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(encoded).hexdigest(),
      'metrics':s.metrics(new),'internal_nodes':sum(not s.leaf(n) for n in sp.nodes(new)),
      'source_sites':len(rr),'guarded_cases':sum(2 if x[1]=='CD' else 1 for x in rr),
      'splices':[[lo,hi,sp.size(v)if v else 0]for(lo,hi),v in edits.items()],
      'retained_instructions':len(mapping),'retained_edges':edges,'macro_test_cases':cases,
      'old_and_new_comparison_durations_equal_in_all_finite_probes':True,
      'residual':'max(c-(old_d+x)-1,0)','status':'source_and_finite_local_checks_pass',
      'scope':'Source syntax/CFG plus finite local checks; ordinary arbitrary-value proof supplied separately. No physical machine certification.'}
    (output/'source_receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path(__file__).with_name('residual'));a=ap.parse_args();construct(a.output)
