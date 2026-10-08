"""Independent recovery of the erased quantum shifts in FastScan.

This checks a structural invariant of every stored differential entry. It does
not infer knot type and does not require the fast composition implementation.
"""
from __future__ import annotations
import json
import random
from pathlib import Path
from bundle_paths import BASELINE_FAST, HERE, baseline_module

FastScan = baseline_module("scan_fast").FastScan
Diagram = baseline_module("diagram").Diagram
best_scan_order = baseline_module("ordering").best_scan_order


class GradingAuditScan(FastScan):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.qshift=[0]
        self.checked_entries=0
        self.checked_terms=0
        self.max_dot_degree=0

    def add_crossing(self,slots,reduce_now=True):
        old_mid,old_q=self.mid,self.qshift
        super().add_crossing(slots,reduce_now=False)
        q=[]
        for v,ma in enumerate(old_mid):
            if ma is None: continue
            for i in (0,1):
                closed=self.algebra.glue(ma,i)[1]
                q.extend(old_q[v]+i+closed-2*label.bit_count()
                         for label in range(1<<closed))
        assert len(q)==len(self.mid)
        self.qshift=q
        self.check_grading()
        if reduce_now:
            self.eliminate()
            self.check_grading()

    def check_grading(self):
        m=len(self.points)//2
        for a,row in enumerate(self.out):
            if not row: continue
            for b,value in row.items():
                k=self.algebra.basis(self.mid[a],self.mid[b])[1]
                expected=k-m+self.qshift[b]-self.qshift[a]
                self.checked_entries+=1
                while value:
                    low=value&-value
                    monomial=low.bit_length()-1
                    d=monomial.bit_count()
                    assert expected==2*d,(a,b,k,m,self.qshift[a],self.qshift[b],d)
                    self.checked_terms+=1
                    self.max_dot_degree=max(self.max_dot_degree,d)
                    value^=low


def main():
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument('--examples',type=Path,default=BASELINE_FAST/'examples')
    p.add_argument('--output',type=Path,default=HERE/'grading_audit_reproduced.json')
    args=p.parse_args()
    names=('unknot','trefoil','figure_eight','hard_unknot_8','conway',
           'kinoshita_terasaka','torus_3_5','unknot_braid40')
    rng=random.Random(202610073)
    records=[]
    for name in names:
        data=json.loads((Path(args.examples)/(name+'.json')).read_text())
        d=Diagram.from_json(data)
        orders=[('input',list(range(d.crossings))),('greedy',best_scan_order(d.pd))]
        if d.crossings<=11:
            order=list(range(d.crossings));rng.shuffle(order)
            orders.append(('seeded_random',order))
        for order_name,order in orders:
            scan=GradingAuditScan(max_objects=50000)
            for i in order: scan.add_crossing(d.pd[i])
            records.append({'case':name,'crossings':d.crossings,'order':order_name,
                'rank':scan.total_rank() if d.crossings else 2,
                'checked_entries':scan.checked_entries,'checked_terms':scan.checked_terms,
                'max_dot_degree':scan.max_dot_degree})
    result={'seed':202610073,'records':records,
        'total_entries':sum(x['checked_entries'] for x in records),
        'total_terms':sum(x['checked_terms'] for x in records),
        'passed':True}
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'}))

if __name__=='__main__':main()
