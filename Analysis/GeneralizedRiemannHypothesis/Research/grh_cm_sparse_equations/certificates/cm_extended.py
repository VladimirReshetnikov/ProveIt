#!/usr/bin/env python3
"""Verify five-root disks in degrees 6–8 and in the finite residual sieve."""
import argparse
import csv
import json
from pathlib import Path
from cm_all_orders import strict_ball_count, threshold, translated_polynomial
from cm_order_678_census import census

CENTERS = [(2,4,7),(2,6,3),(2,6,5),(2,6,7),(3,3,1),(3,3,2),(7,0,6),(11,0,1),
           (13,0,5),(17,0,8),(19,0,7),(23,0,19),(41,0,32)]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--polys',type=Path,default=Path(__file__).with_name('cm-extended-polys.json'))
    ap.add_argument('--residual',type=Path,default=Path(__file__).resolve().parent.parent / 'five' / 'residual.txt')
    ap.add_argument('--csv',type=Path,default=Path('cm-extended-clusters.csv'))
    ap.add_argument('--recompute',action='store_true')
    args=ap.parse_args()
    residual=dict(tuple(map(int,line.split())) for line in args.residual.read_text().splitlines())
    assert len(residual)==66
    orders=census()
    degrees={D:h for h,ds in orders.items() for D in ds}
    assert all(degrees.get(D,h)==h for D,h in residual.items())
    degrees.update(residual)
    data=json.loads(args.polys.read_text())
    assert set(degrees)==set(map(int,data))
    if args.recompute:
        # Set CM_INTERVAL_BITS=1800 before invocation, for the largest D=7987.
        from cm_gen import class_polynomial
        for D in degrees:
            assert class_polynomial(D)==data[str(D)]
    rows=[]
    missing=[]
    for D,h in sorted(degrees.items()):
        poly=data[str(D)]
        assert len(poly)==h+1 and poly[-1]==1
        for p,t,r in CENTERS:
            u=threshold(5,p)
            n=strict_ball_count(translated_polynomial(poly,p,t,r),p,u)
            if n>=5:
                rows.append((D,h,p,t,r,u,n))
                break
        else:
            missing.append(D)
    assert missing==[87,348,432,675]
    with args.csv.open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(('D','h','p','scale_exponent','center','threshold','root_count'))
        writer.writerows(rows)
    for h,ds in orders.items():
        print('degree',h,'orders',len(ds),'five-root disks',len(set(ds)-set(missing)))
    print('input sieve residuals',len(residual),'five-root disks',len(set(residual)-set(missing)))
    print('all distinct class polynomials',len(data),'five-root disks',len(rows))
    print('remaining absolute discriminants',','.join(map(str,missing)))
if __name__=='__main__':
    main()
