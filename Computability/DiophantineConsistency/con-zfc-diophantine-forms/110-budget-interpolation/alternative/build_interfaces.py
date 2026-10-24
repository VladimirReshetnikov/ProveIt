#!/usr/bin/env python3
"""Compile all arithmetic ports. Special-function graphs remain explicit contracts."""
from build_dag import make
from core import CORNERS
from pathlib import Path
import json

def build(kind):
    ring,out,constants=make(CORNERS,shift=True)
    add,mul,sub,c=ring.add,ring.mul,ring.sub,ring.c
    P,A,Y=[out[n] for n in ('P','A','Y')]
    n=mul(add(A,c(1)),Y)
    v,q=ring.v('v'),ring.v('q')
    if kind=='three_powers':
        s,t=ring.v('s'),ring.v('t')
        d=mul(P,v);e=add(s,t,c(1));W=add(mul(e,add(mul(c(2),q),c(1))),s)
        ports=[{'name':'E2','exponent':add(A,c(1)),'value':d},
               {'name':'E2','exponent':n,'value':e},
               {'name':'Eg','base':add(d,c(1)),'exponent':A,'value':W}]
        extra=[];variables=['Q','g','Z','v','q','s','t'];cost='7+2*p2+pg'
    else:
        u,t,j=ring.v('u'),ring.v('t'),ring.v('j')
        d=mul(P,add(n,v,c(1)));e=mul(d,add(u,t,c(1)))
        W=add(mul(e,add(mul(c(2),q),c(1))),mul(d,u),c(1))
        S=sub(sub(e,c(1)),mul(sub(d,c(1)),add(Y,mul(sub(d,c(1)),j))))
        ports=[{'name':'E2','exponent':n,'value':e},
               {'name':'Eg','base':add(d,c(1)),'exponent':A,'value':W}]
        extra=[S];variables=['Q','g','Z','v','q','u','t','j'];cost='8+p2+pg'
        out['S']=S
    out.update(n=n,d=d,e=e,W=W)
    actual=sorted({x['name'] for x in ring.nodes if x['op']=='var'})
    if actual!=sorted(variables): raise RuntimeError('Coordinate ledger mismatch')
    if any(x['op'] not in ['const','var','add','mul','pow_fixed'] for x in ring.nodes):raise RuntimeError('Nonpolynomial port operation')
    obj={'format':'ordinary-polynomial-ports-with-uncompiled-graph-contracts-v1',
         'name':kind,'ordinary_polynomial_claim':False,'tiles':[t.__dict__ for t in CORNERS],
         'constants':constants,'exposed_naturals':variables,'nodes':ring.nodes,
         'outputs':out,'graph_contracts':ports,'ordinary_zero_residuals':extra,
         'conditional_ordinary_variable_count':cost,
         'degree_upper_bounds':{name:ring.degrees[idx] for name,idx in out.items()},
         'node_count':len(ring.nodes)}
    Path(__file__).with_name(kind.upper()+'_INTERFACE.json').write_text(json.dumps(obj,indent=2)+'\n')
    return {k:obj[k] for k in ['name','exposed_naturals','conditional_ordinary_variable_count','node_count','degree_upper_bounds']}

if __name__=='__main__':
    print(json.dumps([build('three_powers'),build('two_powers')],indent=2))
