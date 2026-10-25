#!/usr/bin/env python3
"""Select a measured prefix of the frozen row certificate, without new search."""
import argparse,copy,json
from pathlib import Path
from build_affine import add,scale,mul,terms,decoded,canonical
ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--affine-radix',action='store_true');args=ap.parse_args()
    base=ROOT/('candidate241_affine' if args.affine_radix else 'candidate242');reduced=ROOT/('equation241_affine' if args.affine_radix else 'equation242')
    equation=json.loads((base/'equation.json').read_text());cert=json.loads((reduced/'transformation.json').read_text());rows=[decoded(r) for r in equation['residuals']]
    poly=add(*(mul(r,r) for r in rows));best=None;front=[]
    for index,(i,j,k) in enumerate(cert['final_row_operations']):
        previous=rows[i];rows[i]=add(previous,scale(rows[j],k));poly=add(poly,scale(mul(previous,previous),-1),mul(rows[i],rows[i]))
        height=max(map(abs,poly.values()));nt=len(poly)
        if height<=128446:
            key=(nt,height,index)
            if best is None or key<best[0]:best=(key,index+1,copy.deepcopy(rows),copy.deepcopy(poly))
        if index<20 or index%25==0:front.append({'prefix':index+1,'terms':nt,'height':height})
    if best is None:raise ValueError('No17bit prefix')
    _,count,rows,poly=best;out=ROOT/('equation241_affine_balanced' if args.affine_radix else 'equation242_balanced');out.mkdir(exist_ok=True)
    equation['variant']='unified_bootstrap_affine_balanced'
    equation['residuals']=[{'label':f'row.{i:03d}','terms':terms(r)} for i,r in enumerate(rows)]
    metrics={'variables':len(equation['variables']),'rows':len(rows),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in rows for c in r.values()),'row_support':sum(map(len,rows))}
    cert['final_row_operations']=cert['final_row_operations'][:count]
    for fn,data in [('equation.json',equation),('expanded_polynomial.json',{'schema':'expanded_integer_polynomial_v1','terms':terms(poly)}),('METRICS.json',metrics),('transformation.json',cert),('RESTORATION.json',json.loads((base/'RESTORATION.json').read_text())),('PREFIX_SELECTION.json',{'prefix':count,'rule':'fewest collected terms among this one frozen row sequence at height at most128446; no global optimality','samples':front})]:(out/fn).write_bytes(canonical(data))
    print(json.dumps({'prefix':count,'metrics':metrics},sort_keys=True))
if __name__=='__main__':main()
