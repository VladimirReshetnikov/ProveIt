"""Read a source tile power, emit a closed-graph query certificate, or replay it."""
import argparse,json,sys
from pathlib import Path
from .model import Graph,close
from .normalize import kernel_power
from .query import solve_graph,closed_source_is_cubic
from .replay import verify_graph

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--replay',action='store_true');p.add_argument('--max-kernel-edges',type=int,default=10000)
    args=p.parse_args()
    try:
        data=json.loads(args.input.read_text());source=data['source'] if args.replay else data
        t=Graph.from_dict(source['tile']);n=int(source['exponent_hex'],16);k=source.get('threshold',3)
        if type(k)is not int or not 0<=k<=16:raise ValueError('CLI supports thresholds 0..16')
        g,meta=kernel_power(t,n,k);g=close(g)
        if len(g.edges)>args.max_kernel_edges:raise ValueError('kernel edge resource cap; no graph verdict')
        if args.replay:
            valid=(g.to_dict()==data['kernel'] and verify_graph(g,data['graph_proof'],k))
            result=dict(valid=valid,scope='closed abstract source graph',compression_replay='shared source reconstruction')
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            return 0 if valid else 1
        proof=solve_graph(g,k)
        if not verify_graph(g,proof,k):raise AssertionError('graph certificate failed independent replay')
        result=dict(schema='disconnected-tile-cut-v1',source=source,kernel=g.to_dict(),normalization=meta,
                    original_closure_cubic=closed_source_is_cubic(t),graph_proof=proof,
                    scope='Abstract graph query only; no sphere, ball, or unknot certificate.')
        args.output.write_text(json.dumps(result,indent=2)+'\n');return 0
    except (ValueError,KeyError,TypeError,OSError) as e:
        print(str(e),file=sys.stderr);return 2
if __name__=='__main__':sys.exit(main())
