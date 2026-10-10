"""Run or replay an arithmetic research query; never classify a knot."""
import argparse
from pathlib import Path
from . import HeightModel, optimize_band, replay_band, WorkLimit
from . import minimize_edge_then_span, replay_edge_then_span
from .jsonio import load, dumps


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',help='JSON model or payload with a model field')
    p.add_argument('--radius',type=int,default=1)
    p.add_argument('--lex',action='store_true',help='global edge-then-span objective')
    p.add_argument('--verify',action='store_true',help='replay the supplied answer')
    p.add_argument('--max-work',type=int,default=5_000_000)
    p.add_argument('--output')
    args=p.parse_args()
    try:
        payload=load(args.input)
        model=HeightModel.from_dict(payload.get('model',payload))
        if args.verify:
            answer=payload['answer']
            valid=(replay_edge_then_span(model,answer) if answer.get('schema')=='edge-then-span-v1'
                   else replay_band(model,answer))
            result={'arithmetic_certificate_valid':valid,'knot_verdict':None}
            code=0 if valid else 1
        else:
            answer=(minimize_edge_then_span(model,max_work=args.max_work) if args.lex
                    else optimize_band(model,args.radius,max_work=args.max_work))
            result={'model':model.to_dict(),'answer':answer,'knot_verdict':None};code=0
    except WorkLimit as e:
        result={'status':'INCONCLUSIVE','reason':str(e),'knot_verdict':None};code=2
    except (ValueError,KeyError,TypeError,OSError) as e:
        result={'status':'INVALID_INPUT','reason':str(e),'knot_verdict':None};code=1
    text=dumps(result)
    if args.output:Path(args.output).write_text(text)
    else:print(text,end='')
    return code

if __name__=='__main__':raise SystemExit(main())
