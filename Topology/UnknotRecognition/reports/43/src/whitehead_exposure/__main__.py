"""Small JSON command-line interface; INCONCLUSIVE is not a knot verdict."""
import argparse,json,sys
from pathlib import Path
from .engine import search_presentation
from .braid import recognize_braid
from .slp import barrier_grammar,grammar_graphs,verify_fused_exposure
from .selector import exposure_from_graphs
from .algebra import ResourceLimit

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='action',required=True)
    p=sub.add_parser('presentation');p.add_argument('file',type=Path)
    p.add_argument('--max-letters',type=int,default=200000);p.add_argument('--max-work',type=int,default=10000000)
    p=sub.add_parser('braid');p.add_argument('--strands',required=True,type=int)
    p.add_argument('--word',default='',help='comma-separated signed generators; use --word=-1,2 for a leading minus')
    p.add_argument('--max-letters',type=int,default=200000);p.add_argument('--max-work',type=int,default=10000000)
    p=sub.add_parser('compressed-barrier');p.add_argument('--bits',type=int,default=1000)
    args=parser.parse_args()
    try:
        if args.action=='presentation':
            data=json.loads(args.file.read_text())
            result=search_presentation(data['words'],data['alive'],max_letters=args.max_letters,max_work=args.max_work)
        elif args.action=='braid':
            word=[] if not args.word else [int(x.strip()) for x in args.word.split(',')]
            result=recognize_braid(args.strands,word,max_letters=args.max_letters,max_work=args.max_work)
        else:
            grammar=barrier_grammar(args.bits);p=exposure_from_graphs(grammar_graphs(grammar),(1,2))
            move={key:p[key] for key in ('relation','multiplier','subset')}
            assert verify_fused_exposure(grammar,move,cap=100)
            result={'status':'FREE_RANK_ONE','topological_certificate':False,'power':'2^'+str(args.bits),
                    'grammar_nodes':len(grammar['nodes']),'move':move,'literal_image_cap':100}
        print(json.dumps(result,indent=2))
        return 0
    except ResourceLimit as exc:
        print(json.dumps({'status':'INCONCLUSIVE','reason':str(exc)}));return 0
    except (ValueError,KeyError,TypeError,OSError) as exc:
        parser.error(str(exc))
if __name__=='__main__':sys.exit(main())
