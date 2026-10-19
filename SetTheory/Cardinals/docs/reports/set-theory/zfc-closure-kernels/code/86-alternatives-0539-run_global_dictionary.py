#!/usr/bin/env python3
from pathlib import Path
import sys,json,argparse,time
H=Path(__file__).resolve().parent;R=H.parent/'context_folds/recovered/67/research'
sys.path[:0]=[str(R/'agent_audit/layout_search'),str(R/'agent_logic')]
from verify_reassociation import Decoder,read_json
p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--name',default='prefix_permuted');p.add_argument('--seconds',type=int,default=120);p.add_argument('--maxlen',type=int,default=20);p.add_argument('--maxzero',type=int,default=7);p.add_argument('--maxdepth',type=int,default=39);a=p.parse_args()
import grammar_layout as g
n,r,_=read_json(a.input);g.original=n;g.original_root=r
import dictionary_milp as d
d.HERE=H;d.output_prefix=a.name
result=d.run(a.maxlen,2,a.seconds,a.maxzero,a.maxdepth,False,False,False,())
if 'nodes'in result:
 new=Decoder(result['nodes'],result['root']);old=Decoder(n,r)
 assert old.normal(('N',r))==new.normal(('N',result['root']))
 assert old.graph()==new.graph()
 result['exact_normal_and_guarded_graph_equal']=True
 (H/f'{a.name}_audited.json').write_text(json.dumps(result,indent=2)+'\n')
