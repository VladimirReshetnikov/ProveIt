#!/usr/bin/env python3
"""Naive single-polynomial conversion of the all-length initializer, fully paid."""
if not __debug__:raise RuntimeError('Optimized mode unsupported: checks require assertions')
import argparse,json,pathlib
from bridge_dag import DAG,V,build_uniform_wrapper,uniform_wrapper_cost
from compose_initialization import PairSource,Spliced,output_destination,save_new_output

def build(path,period_y=V,emit=False):
    pair=PairSource(path);d=Spliced(pair,period_y,emit);equations=[]
    oldeq=DAG.eq
    def retain(self,a,b):
        for val in (a,b):
            assert (type(val) is int and 0<=val<self.nodes) or (type(val) is str and (val in self.inputs or val.startswith('C:')))
        equations.append((a,b))
    DAG.eq=retain
    try:build_uniform_wrapper(period_y,dag=d)
    finally:DAG.eq=oldeq
    assert len(equations)==234 and d.equations==0
    sums=[]
    for a,b in equations:
        r=d.sub(a,b);sums.append(d.mul(r,r))
    result=sums[0]
    for square in sums[1:]:result=d.add(result,square)
    d.eq(result,'C:0');receipt=d.receipt()
    base=uniform_wrapper_cost(period_y)
    assert receipt['M']==base['M']+pair.cost['M']+234
    assert receipt['A']==base['A']+pair.cost['A']+467
    assert receipt['equations']==1 and receipt['positive_witnesses']==396
    receipt.update(polynomial_output_wire=result,pair_source_sha256=pair.sha256,
                   original_residuals=234,extra_operations=701,
                   scope='Single polynomial for initialization only, under inherited geometry; exact degree separately certified before parent/endpoint substitution')
    return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--pair-dag',required=True);p.add_argument('--emit',action='store_true');p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    if a.output:output_destination(a.output)
    data=build(a.pair_dag,emit=a.emit);text=json.dumps(data,indent=2)+'\n'
    if a.output:save_new_output(a.output,text)
    print(text,end='')
