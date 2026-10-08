from common import *
from descending_grid import *
from disk_frontier import *
from certified_driver import component_count
import json

def frontier_width(pd,order):
    points=set();width=0
    for j in order:
        for x in pd[j]:
            if x in points:points.remove(x)
            else:points.add(x)
        width=max(width,len(points))
    return width

if __name__=='__main__':
    cases=[]
    for m in range(1,9):
        pd=descending_grid(m);visits=verify_descending(pd)
        assert component_count(pd)==1
        order=bipolar_order(pd)
        ranks=cube_ranks(pd) if m<=3 else None
        if ranks is not None:assert sum(ranks.values())==2
        item=dict(m=m,crossings=m*m,pd=pd,descending_certificate=visits,order=order,
                  input_width=frontier_width(pd,list(range(len(pd)))),
                  certified_order_width=frontier_width(pd,order),cube_ranks=ranks)
        cases.append(item)
        print(m,m*m,item['input_width'],item['certified_order_width'],ranks)
    (ROOT/'results'/'descending_grids.json').write_text(json.dumps(dict(cases=cases),indent=2)+'\n')
