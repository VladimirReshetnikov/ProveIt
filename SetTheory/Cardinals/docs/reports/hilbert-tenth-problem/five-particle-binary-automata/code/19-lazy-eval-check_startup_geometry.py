"""Check all 128 recorded microstep outputs against explicit startup geometry.

This checks the deterministic trace produced by benchmark_universal.py. It does
not execute a source-boundary shortcut or claim startup completion.
"""
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent
CORE='42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61'
SOURCE='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'

def require(ok,detail):
    if not ok:raise RuntimeError(detail)

def main():
    require(sha256((ROOT/'lazy_reversible.py').read_bytes()).hexdigest()==CORE,'core hash')
    raw=(ROOT/'source.json').read_bytes()
    require(sha256(raw).hexdigest()==SOURCE,'source hash')
    data=json.loads(raw)
    m=len(data['controls']);moving=[r for r in data['branches'] if r['delta']]
    D=2*m+4*len(moving);S=2*D+2;Z=10*(4*D+5)+10
    index={q:i for i,q in enumerate(data['controls'])}
    require(moving[0]['source']=='p00001R0T2' and moving[0]['side']==-1,'outbound branch identity')
    def encoded(q):return sorted((-Z-1,0,S,S+2*index[q]+1,Z))
    raw_trace=(ROOT/'universal-startup-trace.json').read_bytes();trace=json.loads(raw_trace)
    require(len(trace)==128,'trace length')
    current=encoded('START')
    for i,record in enumerate(trace):
        require(record['step']==i and record['input']==current,('trace linkage',i))
        if i<3:
            expected=encoded(('h0000B0T1','p00001R0T1','p00001R0T2')[i])
        else:
            anchor=-S-(i-3)
            expected=sorted((-Z-1,0,Z,anchor,anchor+2*m+1))
        require(record['output']==expected,('expected output geometry',i))
        current=expected
    require(current==[-20380381,-1019142,-773897,0,20380380],'final support')
    receipt=dict(status='passed',optimization_level=sys.flags.optimize,evaluator_sha256=CORE,
                 source_sha256=SOURCE,trace_sha256=sha256(raw_trace).hexdigest(),checked_outputs=128,
                 initial_direct_outputs=3,post_dispatch_geometry_outputs=125,
                 zero_based_post_dispatch_anchor='-S-(i-3), for i=3,...,127',head_gap='2m+1',
                 fixed_markers=[-Z-1,0,Z],final_support=current,startup_completed=False,tm_transition_completed=False)
    suffix='-optimized' if sys.flags.optimize else ''
    (ROOT/('startup-geometry-receipt'+suffix+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
