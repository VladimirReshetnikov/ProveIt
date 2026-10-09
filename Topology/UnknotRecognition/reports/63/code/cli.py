"""Source-bound demonstration: python code/cli.py examples/circle.json --cube."""
import argparse,json,sys
from pathlib import Path
from saturation import probe_braid
from kh_oracle import rank_braid,CubeLimit
from source_checker import verify_braid

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source');p.add_argument('--cube',action='store_true',help='Use capped exponential reference after an inconclusive probe');p.add_argument('--proof',help='Write an independently replayed positive probe certificate');p.add_argument('--verify',help='Replay this proof instead of searching');a=p.parse_args()
    try:
        source=json.loads(Path(a.source).read_text());n,b=source['strands'],source['braid']
        if a.verify:
            proof=json.loads(Path(a.verify).read_text());accepted=verify_braid(n,b,proof)
            print(json.dumps({'accepted':accepted}));return 0 if accepted else 1
        result=probe_braid(n,b)
        if a.proof and result['status']=='UNKNOT': Path(a.proof).write_text(json.dumps(result['certificate'],indent=2)+'\n')
        if a.cube and result['status']!='UNKNOT':
            try:
                kh=rank_braid(n,b);result={'status':'UNKNOT' if kh['rank']==1 else 'KNOTTED','method':'small-reference-cube',**kh}
            except CubeLimit as e: result={'status':'INCONCLUSIVE','reason':str(e)}
        print(json.dumps(result,indent=2));return 0
    except (OSError,ValueError,KeyError,TypeError) as e:
        print(f'Invalid input: {e}',file=sys.stderr);return 2
if __name__=='__main__':raise SystemExit(main())
