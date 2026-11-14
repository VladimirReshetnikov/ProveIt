#!/usr/bin/env python3
from pathlib import Path
import sys,json,time,hashlib,argparse
HERE=Path(__file__).resolve().parents[1]/'results'
import reorder_milp as m
def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t
def main():
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=0);p.add_argument('--stop',type=int,default=8);p.add_argument('--limit',type=float,default=30);a=p.parse_args()
    items=json.loads((HERE/'reorder_grammar_shortlist.json').read_text());reports=[]
    for i in range(a.start,min(a.stop,len(items))):
        item=items[i];out=f'reorder_milp_{i}.json';print('START',i,item['order'],item['antecedent_mask'],flush=True);start=time.monotonic()
        try:
            t,objective=m.solve(item['word'],limit=a.limit,outfile=out,warm_tree=tup(item['tree']))
            actual=m.g.cost(t);report=dict(index=i,order=item['order'],antecedent_mask=item['antecedent_mask'],internal_nodes=actual,objective=objective,seconds=time.monotonic()-start,tree_path=out,word=item['word'])
            (HERE/f'reorder_milp_{i}_metadata.json').write_text(json.dumps(report,indent=2)+'\n')
            print('CANDIDATE',i,'actual',actual,'objective',objective,'order',item['order'],'mask',item['antecedent_mask'],flush=True)
        except Exception as e:report=dict(index=i,error=repr(e),seconds=time.monotonic()-start);print('FAIL',report,flush=True)
        reports.append(report);(HERE/f'reorder_milp_batch{a.start}.json').write_text(json.dumps(reports,indent=2)+'\n')

if __name__=='__main__':main()
