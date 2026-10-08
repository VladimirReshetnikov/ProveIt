#!/usr/bin/env python3
"""Optional upstream replay. NOT EXECUTED as part of this release's validation.

Input JSON is a list of {name, pd, order, stage, matchings} records.
Every listed matching is expected to be accepted by the maintained geometry.
"""
from pathlib import Path
import argparse,json,sys,subprocess,hashlib
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from integration.boundary_adapter import ModularBoundaryObserver

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--checkout',type=Path,required=True)
    p.add_argument('--queries',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();base=args.checkout.resolve()
    if (base/'Topology/UnknotRecognition').is_dir():base=base/'Topology/UnknotRecognition'
    module=base/'fast/determinant_research/boundary_tait.py'
    if not module.is_file():p.error('checkout has no maintained boundary_tait.py')
    sys.path[:0]=[str(base/'fast/determinant_research'),str(base/'fast'),str(base/'reports/26')]
    try:from boundary_tait import BoundaryTait
    except ImportError as exc:p.error(f'upstream imports failed: {exc}')
    raw=args.queries.read_bytes();records=json.loads(raw);completed=[]
    if not isinstance(records,list):p.error('query JSON must be a list')
    for record in records:
        pd=tuple(tuple(c) for c in record['pd']);order=tuple(record['order'])
        if sorted(order)!=list(range(len(pd))):raise ValueError('order must be a crossing permutation')
        matchings=[tuple(tuple(pair) for pair in m) for m in record['matchings']]
        geometry=BoundaryTait(pd,order,record['stage'])
        reference=[geometry.evaluate(m) for m in matchings]
        modular=ModularBoundaryObserver(geometry)
        static=[modular.evaluate(m) for m in matchings]
        dynamic=modular.evaluate_many(matchings)
        if reference!=static or reference!=dynamic:
            raise AssertionError(f"value or metadata mismatch: {record.get('name','unnamed')}")
        completed.append(dict(name=record.get('name','unnamed'),queries=len(matchings)))
    try:revision=subprocess.check_output(['git','-C',str(base),'rev-parse','HEAD'],text=True).strip()
    except (subprocess.CalledProcessError,OSError):revision=None
    result=dict(schema='upstream-boundary-replay-v1',revision=revision,
                boundary_source_sha256=hashlib.sha256(module.read_bytes()).hexdigest(),
                input_sha256=hashlib.sha256(raw).hexdigest(),records=completed,
                accepted_queries=sum(r['queries'] for r in completed),success=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
