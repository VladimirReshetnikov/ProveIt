#!/usr/bin/env python3
"""Reject unsupported inputs and corrupted algebra/tail/source evidence under -O."""
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import tempfile
sys.dont_write_bytecode=True
HERE=Path(__file__).absolute().parent
sys.path.insert(0,str(HERE))
sys.path.insert(0,str(HERE.parent))
import exact_coefficients as exact
import positive_tail as tail
import verify_manifest as manifest
import verify_source_data as provenance


def run_tests():
    accepted, rejected = [], []

    def good(label,condition):
        if not condition:
            raise RuntimeError(label)
        accepted.append(label)

    def bad(label,call):
        try:
            call()
        except (ValueError,TypeError,ArithmeticError,OSError):
            rejected.append(label)
            return
        raise RuntimeError('expected rejection did not occur: '+label)

    d=exact.coeffs(6,1)
    exact.verify_reference(d)
    good('printed d0,d1,d2 exact formulas',True)
    for j in range(3):
        damaged=copy.deepcopy(d)
        a,b=damaged[j].get(0,(Q(0),Q(0)))
        damaged[j][0]=(a+Q(1,10**20),b)
        bad('corrupted coefficient d'+str(j),lambda damaged=damaged:exact.verify_reference(damaged))
    bad('missing reference coefficient',lambda:exact.verify_reference(d[:2]))
    bad('wrong reference container',lambda:exact.verify_reference(tuple(d)))
    good('coefficient order zero',exact.coeffs(0,1)==[{0:exact.ONE}])
    good('high supported mode',exact.coeffs(0,1000)==[{0:exact.ONE}])
    good('maximum supported order',len(exact.coeffs(12,1))==13)
    good('truncation compatibility',exact.coeffs(4,2)==exact.coeffs(6,2)[:5])
    good('Bernoulli convention and values',exact.bernoulli(6)==[Q(1),Q(-1,2),Q(1,6),Q(0),Q(-1,30),Q(0),Q(1,42)])
    for value in (-1,13,True,False,1.0,'2',None,Q(1)):
        bad('unsupported coefficient order '+repr(value),lambda value=value:exact.coeffs(value,1))
    for value in (0,-1,1001,True,1.0,'1',None,Q(1)):
        bad('unsupported harmonic mode '+repr(value),lambda value=value:exact.coeffs(2,value))
    for value in (-1,14,True,1.0,None):
        bad('unsupported Bernoulli order '+repr(value),lambda value=value:exact.bernoulli(value))
    for n in range(1,35):
        T=4*n+60
        value=tail.tail_bound(n,T)
        tail.check_bound(n,T,value)
        good('rational tail inequality n='+str(n),0<value<Q(1,10**35))
    value=tail.tail_bound(17,128)
    for label,damaged in [('negative',-value),('zero',Q(0)),('off by rational epsilon',value+Q(1,10**100)),('rounded float',float(value))]:
        bad('corrupted tail '+label,lambda damaged=damaged:tail.check_bound(17,128,damaged))
    for threshold in (Q(0),Q(-1),value,value/2,float(value)):
        bad('invalid or unmet threshold '+repr(threshold),lambda threshold=threshold:tail.check_bound(17,128,value,threshold))
    for n in (0,-1,1001,True,1.0,'1',None,Q(1)):
        bad('unsupported n '+repr(n),lambda n=n:tail.tail_bound(n,64))
    for T in (0,1,-1,10001,True,64.0,'64',None,Q(64)):
        bad('unsupported T '+repr(T),lambda T=T:tail.tail_bound(1,T))
    good('small exact tail formula',tail.tail_bound(1,2)==Q(8))
    good('near diagonal supported input',tail.tail_bound(1000,1001)>0)
    with tempfile.TemporaryDirectory(prefix='report187-math-guards-') as temporary:
        root=Path(temporary)
        (root/'data').mkdir()
        payload=b'{"fixture":"bounded attributed data"}\n'
        path=root/'data/oeis_prefix.json'
        path.write_bytes(payload)
        def receipt():
            return {'retrieved_utc_date':'2026-10-03','files':{'data/oeis_prefix.json':{
                'bytes':len(payload),'sha256':__import__('hashlib').sha256(payload).hexdigest()}}}
        receipt_path=root/'data/SOURCE_DATA_HASHES.json'
        def put(value):
            receipt_path.write_text(json.dumps(value,sort_keys=True))
        put(receipt())
        good('valid bounded fixture receipt',provenance.verify(root)['status']=='PASS')
        path.write_bytes(payload+b' ')
        bad('altered source fixture',lambda:provenance.verify(root))
        path.write_bytes(payload)
        for label,mutate in [
            ('wrong byte count',lambda x:x['files']['data/oeis_prefix.json'].__setitem__('bytes',len(payload)+1)),
            ('boolean byte count',lambda x:x['files']['data/oeis_prefix.json'].__setitem__('bytes',True)),
            ('changed hash',lambda x:x['files']['data/oeis_prefix.json'].__setitem__('sha256','0'*64)),
            ('wrong source date',lambda x:x.__setitem__('retrieved_utc_date','2000-01-01')),
            ('extra receipt field',lambda x:x['files']['data/oeis_prefix.json'].__setitem__('extra',1)),
            ('removed fixture',lambda x:x['files'].clear()),
            ('extra fixture',lambda x:x['files'].__setitem__('data/unrelated',{})),
        ]:
            altered=receipt()
            mutate(altered)
            put(altered)
            bad('corrupted receipt '+label,lambda:provenance.verify(root))
        receipt_path.write_text('{"retrieved_utc_date":"2026-10-03","files":{},"files":{}}')
        bad('duplicate receipt key',lambda:provenance.verify(root))
        put(receipt())
        path.unlink()
        bad('missing source fixture',lambda:provenance.verify(root))
    return {'status':'PASS','acceptance_tests':len(accepted),'rejection_tests':len(rejected),
            'total_tests':len(accepted)+len(rejected),
            'accepted':accepted,'rejected':rejected,
            'removable_assertions_used':False,'floating_arithmetic_used_for_proofs':False}


if __name__=='__main__':
    print(json.dumps(run_tests(),sort_keys=True,indent=2,allow_nan=False))
