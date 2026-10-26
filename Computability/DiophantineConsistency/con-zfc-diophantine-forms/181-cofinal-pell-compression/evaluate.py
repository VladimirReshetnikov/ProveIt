#!/usr/bin/env python3
"""Evaluate a delivered polynomial at a specified integer tuple; no search."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from polynomial import poly,evaluate

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('profile',choices=['229','228','207','206'])
    ap.add_argument('point',help='JSON integer array file, or - for stdin')
    ap.add_argument('--residuals',action='store_true')
    a=ap.parse_args()
    paths={'229':'equations/P229_balanced/equation.json',
           '228':'equations/P228_compact/equation.json',
           '207':'pooling/oriented_split/principal207.json',
           '206':'pooling/oriented_pool/principal206.json'}
    eq=json.loads((ROOT/paths[a.profile]).read_text())
    point=json.load(sys.stdin) if a.point=='-' else json.loads(Path(a.point).read_text())
    if not isinstance(point,list) or len(point)!=len(eq['variables']) or any(type(x) is not int for x in point):
        raise ValueError('point must be a JSON array of exactly '+str(len(eq['variables']))+' integers; booleans are not integers here')
    values=[evaluate(poly(r['terms']),point) for r in eq['residuals']]
    out={'profile':a.profile,'value':sum(x*x for x in values)}
    if a.residuals:out['residuals']=values
    print(json.dumps(out))

if __name__=='__main__':main()
