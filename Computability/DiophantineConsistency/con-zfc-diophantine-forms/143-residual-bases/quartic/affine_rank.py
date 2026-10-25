#!/usr/bin/env python3
"""Exact modular lower bounds on rational quadratic-part row rank."""
import argparse,json,math
from pathlib import Path
PRIME=1000003
if any(PRIME%d==0 for d in range(2,math.isqrt(PRIME)+1)):raise ValueError("modulus is not prime")
def rank(rows):
    pivots={};transcript=[]
    for i,row in enumerate(rows):
        r={tuple(m):c%PRIME for c,m in row['terms'] if len(m)==2 and c%PRIME}
        while r:
            m=min(r);c=r[m]
            if m not in pivots:
                inv=pow(c,PRIME-2,PRIME);pivots[m]={x:v*inv%PRIME for x,v in r.items()};transcript.append({'source_row':i,'pivot_monomial':list(m),'pivot_value':c});break
            for x,v in pivots[m].items():
                r[x]=(r.get(x,0)-c*v)%PRIME
                if not r[x]:del r[x]
    return {'prime':PRIME,'rank_mod_prime':len(pivots),'pivot_certificate':transcript}
def main():
    p=argparse.ArgumentParser();p.add_argument('--release',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);a=p.parse_args();manifest=json.loads((a.release/'ENDPOINTS.json').read_text());out={}
    for name,item in manifest['endpoints'].items():
        d=json.loads((a.release/item['directory']/'equation.json').read_text());n=len(d['variables'])
        if n!=278:continue
        s=json.loads((a.release/item['source']).read_text());old=rank(s['residuals']);new=rank(d['residuals'])
        if old['rank_mod_prime']!=188 or new['rank_mod_prime']!=188 or len(d['residuals'])!=188:raise ValueError('rank target')
        out[name]={'source_rows':len(s['residuals']),'source_quadratic_rank_lower_bound':old,'final_rows':len(d['residuals']),'final_quadratic_rank':new,'conclusion':'No nonzero rational linear combination of the final 188 residuals is affine. This is a row-span statement, not a general ideal or global variable lower bound.'}
    if not out:raise ValueError('no dimension endpoint')
    text=json.dumps({'status':'pass','affine_rank':out},indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
