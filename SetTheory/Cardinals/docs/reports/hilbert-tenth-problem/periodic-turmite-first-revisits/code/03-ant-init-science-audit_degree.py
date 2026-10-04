#!/usr/bin/env python3
"""Independent total-degree upper bounds on every composed source expression.
Also tracks an exact pure-W highest homogeneous term when it is certified.
No gigantic numeral coefficient is expanded.
"""
if not __debug__:raise RuntimeError('Optimized mode unsupported: checks require assertions')
import argparse,array,json,pathlib
from bridge_dag import DAG,build_uniform_wrapper,V
from compose_initialization import PairSource,Spliced,output_destination,save_new_output

def check(path):
    degrees=array.array('I');pure=[];coef=[];eqs=[]
    def info(x):
        if type(x) is int:return degrees[x],pure[x],coef[x]
        if x=='W':return 1,True,1
        if x.startswith('C:'):
            c=x[2:]
            return 0,True,int(c) if c.lstrip('-').isdigit() else None
        return 1,False,None
    def combine(op,x,y):
        dx,px,cx=x;dy,py,cy=y
        if op=='*':
            cc=cx*cy if cx is not None and cy is not None else None
            return dx+dy,px and py and cc!=0,cc
        if dx>dy:return x
        if dy>dx:return (dy,py,(-cy if cy is not None and op=='-' else cy))
        cc=None if cx is None or cy is None else cx+cy if op=='+' else cx-cy
        return dx,px and py and cc!=0,cc
    oldgate=DAG.gate;oldeq=DAG.eq
    def gate(self,op,a,b):
        got=combine(op,info(a),info(b));out=oldgate(self,op,a,b)
        assert out==len(degrees)
        degrees.append(got[0]);pure.append(got[1]);coef.append(got[2]);return out
    def eq(self,a,b):
        got=combine('-',info(a),info(b));oldeq(self,a,b)
        eqs.append({'index':len(eqs),'degree_upper_bound':got[0],
                    'exact_leading_pure_W':got[1] and got[2] is not None and got[2]!=0,
                    'leading_W_coefficient':got[2] if got[1] else None,
                    'left_degree':info(a)[0],'right_degree':info(b)[0]})
    DAG.gate=gate;DAG.eq=eq
    try:
        d=Spliced(PairSource(path));receipt=build_uniform_wrapper(dag=d)
    finally:DAG.gate=oldgate;DAG.eq=oldeq
    upper=max(e['degree_upper_bound'] for e in eqs)
    tops=[e for e in eqs if e['degree_upper_bound']==upper]
    assert upper==2*V and len(tops)==2
    assert all(e['exact_leading_pure_W'] and e['leading_W_coefficient']==-1 for e in tops)
    assert len(eqs)==234 and len(degrees)==2306387
    return {'status':'PASS','source_dag_sha256':receipt['dag_sha256'],'residual_degree_upper_bound':upper,
            'maximal_residuals':tops,'sum_of_squares_exact_degree':2*upper,
            'sum_of_squares_leading_term':{'coefficient':2,'variable':'W','exponent':2*upper},
            'naive_extra_operations':3*len(eqs)-1,'naive_total_operations':receipt['total']+3*len(eqs)-1,
            'naive_extra_M':len(eqs),'naive_extra_A':2*len(eqs)-1,
            'positive_witnesses':receipt['positive_witnesses'],'all_residual_bounds':eqs,
            'scope':'Total degree in inherited initializer ports and its 396 new positive witnesses, with prescribed fixed coefficients. No parent-history or endpoint substitution, strict constant expansion, or optimized sum-of-squares count.'}
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--pair-dag',required=True);p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    if a.output:output_destination(a.output)
    result=check(a.pair_dag);text=json.dumps(result,indent=2)+'\n'
    if a.output:save_new_output(a.output,text)
    print(text,end='')
