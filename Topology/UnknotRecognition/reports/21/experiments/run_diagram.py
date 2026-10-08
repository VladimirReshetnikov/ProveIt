"""Standalone demonstration CLI; source-derived fixture, not the production CLI."""
from common import *
from certified_driver import certified_homology, recognize_certified
from fastunknot.geometry import ScanLimit
import argparse,json,sys

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--json',type=Path,help='JSON object with pd, or with strands and word')
    p.add_argument('--strands',type=int)
    p.add_argument('--word',help='comma-separated braid generators, e.g. --word=1,-2,1,-2')
    p.add_argument('--mode',choices=['adaptive','always','auto','terminal'],default='adaptive')
    p.add_argument('--homology',action='store_true',help='allow links and return ranks without a knot verdict')
    p.add_argument('--max-objects',type=int)
    p.add_argument('--seconds',type=float)
    p.add_argument('--input-order',action='store_true',help='retain input order, using safe per-stage fallback')
    args=p.parse_args()
    try:
        if args.json:
            data=json.loads(args.json.read_text())
            pd=data['pd'] if 'pd' in data else braid_pd(data['strands'],data['word'])
        elif args.strands is not None and args.word is not None:
            pd=braid_pd(args.strands,[int(x) for x in args.word.split(',') if x.strip()])
        else:p.error('supply --json or both --strands and --word')
        operation=certified_homology if args.homology else recognize_certified
        result=operation(pd,mode=args.mode,order=list(range(len(pd))) if args.input_order else None,
                         max_objects=args.max_objects,seconds=args.seconds)
        print(json.dumps(result,indent=2))
    except ScanLimit as error:
        print(json.dumps(dict(status='UNKNOWN_RESOURCE_LIMIT',error=str(error))))
        sys.exit(2)
    except (ValueError,KeyError,TypeError) as error:
        print(json.dumps(dict(status='INVALID_OR_UNSUPPORTED_INPUT',error=str(error))))
        sys.exit(2)
