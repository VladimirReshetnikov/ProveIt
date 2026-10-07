#!/usr/bin/env python3
"""Deliberate mathematical/source corruption tests, active under python -O."""
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path
import json
import shutil
import sys
import tempfile
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
from certify_amplitudes import compute,pi_bounds,exp_half_bounds,sqrt_bounds,fixed_decimal,check
from check_exact import check_bfile,check_casoratian,exact_checks
from audit_positive_sum import positive_sum_state,validate_certificate
from formal_series import Ring,forward_coefficients,check_by_log_ratios,check_inverse_composition,inverse_coefficients,PUBLISHED_C,PUBLISHED_B,PUBLISHED_INVERSE
from check_common_truncations import common_truncation,generate as check_truncations
import verify_source_data
from verify_manifest import load_json,read_regular


def run_tests():
    rejected=[]
    def bad(label,call):
        try:
            call()
        except (ArithmeticError,RuntimeError,ValueError,KeyError,OSError,TypeError):
            rejected.append(label)
        else:
            raise ArithmeticError('guard failed to reject: '+label)
    cert=load_json(read_regular(ROOT/'certificates/amplitude_certificate.json'))
    state=positive_sum_state(10000)
    check(validate_certificate(cert,state)['status']=='PASS','valid certificate rejected')
    for label,mutate in [
        ('N',lambda c:c.update(N=9999)),
        ('digits',lambda c:c.update(digits=69)),
        ('final term',lambda c:c['sequences']['floor'].update(a_N='0')),
        ('final sum',lambda c:c['sequences']['ceiling'].update(sum_N='0')),
        ('prefix',lambda c:c['sequences']['floor']['prefix'].__setitem__(3,99)),
        ('lower bound',lambda c:c['sequences']['floor']['A'].__setitem__(0,'0.75')),
        ('upper bound',lambda c:c['sequences']['ceiling']['A'].__setitem__(1,'1.2')),
        ('width',lambda c:c['sequences']['floor'].update(width_A_upper='0'))]:
        corrupt=deepcopy(cert);mutate(corrupt)
        bad('certificate '+label,lambda corrupt=corrupt:validate_certificate(corrupt,state))
    for key in ('C_Bessel','c_exp'):
        corrupt=deepcopy(cert);corrupt['sequences']['floor'][key][0]='0'
        bad('transformed constant '+key,lambda corrupt=corrupt:check_truncations(corrupt))
    bad('crossed common truncation boundary',lambda:common_truncation(F(149,100),F(151,100),1))
    check(common_truncation(F(1491,1000),F(1499,1000),2)=='1.49','valid common truncation rejected')
    for val in (0,1,-1,2.5,True):bad('invalid N '+repr(val),lambda val=val:compute(val))
    for val in (0,-2,2.5):bad('invalid digits '+repr(val),lambda val=val:compute(2,val))
    for val in (0,-1,False):
        bad('pi terms '+repr(val),lambda val=val:pi_bounds(val))
        bad('exp terms '+repr(val),lambda val=val:exp_half_bounds(val))
    bad('negative square root',lambda:sqrt_bounds(F(-1)))
    bad('negative decimal digits',lambda:fixed_decimal(F(1),-1))
    p,q=pi_bounds();e,f=exp_half_bounds()
    check(F(3)<p<q<F(22,7) and F(1)<e<f<F(2),'elementary enclosures invalid')
    for x in (F(0),F(2),F(49,9)):
        a,b=sqrt_bounds(x,25);check(a*a<=x<b*b,'sqrt bounds invalid')
    for x in (F(-5,7),F(2,3),F(0)):
        check(F(fixed_decimal(x,12))<=x<=F(fixed_decimal(x,12,True)),'outward decimal enclosure invalid')
    bfile=read_regular(ROOT/'data/b065094.txt').decode('ascii')
    for label,text in [('value',bfile.replace('4 5\n','4 6\n',1)),('duplicate',bfile+'1000 1\n'),
                       ('missing', '\n'.join(bfile.splitlines()[1:])),('column',bfile+'1001 1 2\n')]:
        bad('b-file '+label,lambda text=text:check_bfile(text,'floor'))
    for j in range(1,7):
        wrong=PUBLISHED_C.copy();wrong[j]+=F(1,100)
        bad('formal forward c'+str(j),lambda wrong=wrong:check_by_log_ratios(wrong))
    for j in range(5):
        wrong=PUBLISHED_INVERSE.copy();wrong[j]+=F(1,100)
        bad('inverse coefficient '+str(j),lambda wrong=wrong:check_inverse_composition(PUBLISHED_C,wrong))
    r=Ring(5)
    for label,call in [('power nonunit',lambda:r.power_unit(r.const(2),F(1,2))),
                       ('log nonunit',lambda:r.log(r.const(0))),('exp nonzero constant',lambda:r.exp(r.const(1))),
                       ('negative ring order',lambda:Ring(-1)),('noninteger forward order',lambda:forward_coefficients(1.5)),
                       ('short inverse input',lambda:inverse_coefficients(PUBLISHED_B,8)),
                       ('Casoratian sign',lambda:check_casoratian([0,F(1),F(2)],[(0,0),(1,0),(2,1)],1))]:
        bad(label,call)
    with tempfile.TemporaryDirectory(prefix='rounded-mean-corruption-') as temporary:
        fixture=Path(temporary)
        for name in list(verify_source_data.EXPECTED)+['data/SOURCE_DATA_HASHES.json']:
            p=fixture/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(read_regular(ROOT/name))
        check(verify_source_data.verify(fixture)['status']=='PASS','valid source receipt rejected')
        p=fixture/'data/b065094.txt';original=p.read_bytes();p.write_bytes(original+b'\n')
        bad('altered source data',lambda:verify_source_data.verify(fixture))
        p.write_bytes(original)
        receipt=fixture/'data/SOURCE_DATA_HASHES.json'
        data=load_json(receipt.read_bytes());data['files'].pop('data/b065095.txt');receipt.write_text(json.dumps(data))
        bad('missing source receipt entry',lambda:verify_source_data.verify(fixture))
        receipt.write_bytes(read_regular(ROOT/'data/SOURCE_DATA_HASHES.json'))
        prefixes=fixture/'data/oeis_prefixes.json';data=load_json(prefixes.read_bytes());data['A065094']['terms'][2]=9;prefixes.write_text(json.dumps(data))
        bad('altered official prefix mathematics',lambda:exact_checks(fixture))
    return {'status':'PASS','negative_tests':len(rejected),'assertions_required':False,
            'guards':['certificate state, endpoints and width','b-file and prefix','formal forward and inverse',
                      'symbolic Casoratian','source receipts','elementary rational enclosures']}


if __name__=='__main__':
    print(json.dumps(run_tests(),indent=2,sort_keys=True))
