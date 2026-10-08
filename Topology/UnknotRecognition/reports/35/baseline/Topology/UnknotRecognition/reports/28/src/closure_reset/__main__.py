from __future__ import annotations
import argparse,json,sys
from .diagram import braid_pd
from .driver import recognize_pd

def main():
    p=argparse.ArgumentParser(description='Optional classical-closure reset recognizer')
    p.add_argument('input'); p.add_argument('--max-objects',type=int,default=200000)
    p.add_argument('--seconds',type=float,default=None); p.add_argument('--check-d2',action='store_true')
    args=p.parse_args()
    try:
        with open(args.input,encoding='utf-8') as f: obj=json.load(f)
        pd=obj['pd'] if 'pd' in obj else braid_pd(obj['strands'],obj['word'])
        result=recognize_pd(pd,max_objects=args.max_objects,seconds=args.seconds,check_d_squared=args.check_d2)
        print(json.dumps(result,sort_keys=True,indent=2))
        return 3 if result['status']=='UNKNOWN' else 0
    except (ValueError,KeyError,TypeError,OSError) as exc:
        print(json.dumps({'status':'INVALID','reason':str(exc)})); return 2
if __name__=='__main__': sys.exit(main())
