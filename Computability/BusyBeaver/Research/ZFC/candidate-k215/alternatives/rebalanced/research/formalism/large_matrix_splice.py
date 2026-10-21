#!/usr/bin/env python3
"""Build and check an experimental late-matrix-inflation source.

Uses the packet's pinned baseline and unchanged vendored source-splice utility.
Python 3 standard library only. This is a source experiment, not an accepted
binary machine or a completed native-calculus-to-ZFC calibration.
"""
from pathlib import Path
from itertools import product
import argparse, hashlib, json, sys

PIN = '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
SPLICE_PIN = '79036d8b1d85c37927fd9db67c49a8d8c3f8684359d4598c009f31d6c1a790ba'
HERE = Path(__file__).resolve().parent
PACKET = HERE.parents[1]

def sha(raw): return hashlib.sha256(raw).hexdigest()
def copyadd(i,j,k):
    return ((('CD',i),(('CI',j),(('CI',k),('CC',3)))),
            (('CD',k),(('CI',i),('CC',2))))
def clear(i): return (('CD',i),('CC',1))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,default=PACKET/'baseline/sites215.json',
                    help='Pinned accepted K215 source; defaults to the included baseline')
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args(); a.output.mkdir(parents=True,exist_ok=True)
    splice_raw=(HERE/'vendor/source_splice.py').read_bytes()
    assert sha(splice_raw)==SPLICE_PIN, 'Unexpected vendored splice utility'
    sys.path.insert(0,str(HERE/'vendor'))
    import source_splice as sp
    raw=a.baseline.read_bytes(); assert sha(raw)==PIN, 'Unexpected baseline source'
    rows=json.loads(raw); old=sp.parse(rows)
    oldg=sp.cfg_intervals(rows); assert oldg==sp.cfg_arithmetic(rows)
    pre=sp.serial([copyadd(4,3,6),copyadd(5,3,6),('CI',3)])
    first=sp.serial(sp.closed_forest(old,2643,2723))
    edits={(2643,2723):(pre,first),
           (4556,4560):clear(3), (4560,4572):clear(5),
           (4572,4578):None, (4578,4590):clear(4)}
    assert all(v is None or sp.boundary(v)==(0,0,False) for v in edits.values())
    new=sp.apply_closed_splices(old,edits); rr=sp.sites(new)
    g=sp.cfg_intervals(rr); assert g==sp.cfg_arithmetic(rr)
    # Map all unchanged primitives outside the edited closed intervals.
    mapping={}; replacements={}; cursor=0
    for i in range(len(rows)):
        covered=next(((lo,hi,v) for (lo,hi),v in edits.items() if lo<=i<hi),None)
        if covered:
            lo,hi,v=covered
            if i==lo:
                count=0 if v is None else sp.size(v)
                replacements[lo]=(cursor,count); cursor+=count
        else: mapping[i]=cursor; cursor+=1
    assert cursor==len(rr)
    def redirect(i):
        if i in mapping:return mapping[i]
        for (lo,hi),v in edits.items():
            if lo<=i<hi:
                assert i==lo, ('outside edge enters edited interior',i,lo,hi)
                return replacements[lo][0] if v is not None else redirect(hi%len(rows))
        raise AssertionError(i)
    edges=0
    for i,j in mapping.items():
        op,operand,to=oldg[i]
        assert tuple(rr[j][1:])==tuple(rows[i][1:])
        assert g[j]==(op,operand,tuple(redirect(k) for k in to))
        edges+=len(to)
    # The original first bundle factor is literally retained after the insertion.
    at=replacements[2643][0]+sp.size(pre)
    assert [x[1:] for x in rr[at:at+80]]==[tuple(x[1:]) for x in rows[2643:2723]]
    def run(macro,reg):
        r=sp.sites((macro,('CH',None))); cg=sp.cfg_intervals(r)
        assert cg==sp.cfg_arithmetic(r)
        pc=0; reg=list(reg)
        for step in range(10000):
            op,k,to=cg[pc]
            if op=='CH':return reg
            if op=='CI':reg[k]+=1;pc=to[0]
            elif op=='CD':b=int(reg[k]>0);reg[k]-=b;pc=to[b]
            else:pc=to[0]
        raise AssertionError('probe limit exceeded')
    cases=0
    cleanup=sp.serial([clear(3),clear(5),clear(4)])
    for A,B,C in product(range(12),range(12),range(12)):
        initial=[13,17,19,C,A,B,0,0,23]
        expected=initial.copy();expected[3]=C+A+B+1
        assert run(pre,initial)==expected
        after=expected.copy(); after[3]=after[4]=after[5]=0
        assert run(cleanup,expected)==after
        cases+=1
    source=sp.compact(rr); (a.output/'large_matrix_source.json').write_bytes(source)
    result={
        'status':'SOURCE_AND_FINITE_MACRO_INTERFACE_PASS',
        'scope':'Exact source splice, two full CFG resolvers, outside-edge preservation and finite macro probes. No allocated binary table, full runtime, blank initialization or native-calculus-to-ZFC lower bridge.',
        'baseline_source_sha256':sha(raw),'source_sha256':sha(source),
        'vendored_source_splice_sha256':sha(splice_raw),
        'metrics':sp.metrics(new),'guarded_cases':sum(2 if o=='CD' else 1 for _,o,_ in rr),
        'new_distinct_source_nodes':len(sp.nodes(new)-sp.nodes(old)),
        'removed_distinct_source_nodes':len(sp.nodes(old)-sp.nodes(new)),
        'retained_primitives_checked':len(mapping),'retained_guarded_edges_checked':edges,
        'literal_first_bundle_factor_leaves':80,'macro_probe_cases':cases,
        'splices':[[lo,hi,0 if v is None else sp.size(v)] for (lo,hi),v in edits.items()],
        'AX_semantics':{'logical_rows':'unchanged parameters A=oldD+x, B=oldH+y, c=raw selector residual, U=oldD',
                        'bundle':'unconditionally emit bundle222(A,B,c+A+B+1)',
                        'exit':'same ten stack entries as before; D=H=0; selector and scratch counters zero'},
        'missing_obligation':'Prove restricted native calculus, whose only emitted atomic-vacuity instances have binder c>A+B, is equiconsistent with ZFC. Ordinary FOL matrix-padding does not discharge this obligation.'}
    (a.output/'large_matrix_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
