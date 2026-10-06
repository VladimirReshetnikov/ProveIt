#!/usr/bin/env python3
"""Explicit checks remain active under python -O; no optional dependencies."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from exact_euler import MAX_INDEX,bounded_index,decimal,euler_step,product_step,diagonal,coefficients,array_entry
from coordinate_series import generate,KNOWN
ROOT=Path(__file__).resolve().parents[1]

def equal(a,b,label):
    if a!=b: raise ArithmeticError('check failed: '+label)

def rejects(fn,label):
    try: fn()
    except ValueError: return
    raise ArithmeticError('missing validation: '+label)

def run(cap):
    bounded_index(cap)
    if cap<414: raise ValueError('test cap must be from 414 to 640')
    equal([str(x) for x in generate(9)],KNOWN,'exact formal Fatou coefficients')
    rejects(lambda:generate(13),'formal order cap')
    values=diagonal(cap);strings=[decimal(x) for x in values]
    fixture=json.loads((ROOT/'data/exact414.json').read_text())
    equal(strings[:415],fixture['diagonal'],'independent exact414 fixture')
    source=json.loads((ROOT/'sources/A290354_first22.json').read_text())
    equal(strings[:22],source['values'],'OEIS displayed n=0..21')
    row=[0,1]+[0]*11;product=row[:]
    for h in range(1,13):
        row=euler_step(row);product=product_step(product)
        equal(row,product,'independent product degree12 height'+str(h))
        equal([decimal(v) for v in row[1:]],fixture['small_rows_h1_to_h12'][h-1][1:],'small row fixture')
    equal(diagonal(0),[1],'a0 separate convention')
    equal(coefficients(0,20),[0],'Fh constant zero')
    equal(coefficients(5,0),[0,1,0,0,0,0],'F0')
    equal(coefficients(5,1),[0,1,1,1,1,1],'F1')
    equal(array_entry(0,0),1,'A(0,0) convention')
    equal(array_entry(0,10),1,'A(0,m) convention')
    equal(array_entry(3,3),6,'A(3,3)')
    equal(decimal(10**3000),'1'+'0'*3000,'long safe rendering')
    equal(decimal(-10**3000),'-1'+'0'*3000,'negative safe rendering')
    for bad in (-1,641,True,1.5): rejects(lambda:bounded_index(bad),'index')
    for bad in ([],[1],[0,-1],[0,True],[0,1.5]): rejects(lambda:euler_step(bad),'row')
    rejects(lambda:product_step([0]*22),'product degree cap')
    encoded=json.dumps(strings,separators=(',',':')).encode()
    return {'status':'passed','cap':cap,'diagonal_sha256':sha256(encoded).hexdigest(),
            'last_digits':len(strings[-1]),'independent_fixture_n':[0,414],
            'external_OEIS_comparison_n':[0,21],'product_check_degree':12,'product_check_height':12}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cap',type=int,default=640)
    args=ap.parse_args()
    try: answer=run(args.cap)
    except ValueError as exc: ap.error(str(exc))
    print(json.dumps(answer,sort_keys=True,indent=2))
