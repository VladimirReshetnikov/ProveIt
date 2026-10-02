#!/usr/bin/env python3
"""Portable exact schema tests for the narrowly allowed tail_sum extension.
Usage: python selftest_multiplier_portable.py SOURCE --output RECEIPT"""
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
import argparse,hashlib,json,time
import check
import check_fast
import check_extended


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    started=time.time();source=args.source
    cores,catalog_hash=check.read_catalog(source/'cores.txt');require=check.require
    code,rows=cores[762]
    canonical_path=source/'tail-sum-cubic/certificate_762.json'
    canonical_raw=canonical_path.read_bytes();canonical=json.loads(canonical_raw)
    record=check_extended.check_one((str(source),762,code,rows,'tail-sum-cubic'))
    # Fixed regression totals from the independently approved canonical 762
    # certificate. No original producer candidate or prior receipt is needed.
    require(record['square_count']==648 and record['positive_remainder_term_count']==3144,
            'Canonical 762 regression totals differ from the approved release')
    tests=[]
    with TemporaryDirectory(prefix='tail-sum-schema-selftest-') as temp:
        for name in ('two-sink-cubic','tail-sum-cubic'):(Path(temp)/name).mkdir()
        base={'rows':[0]*5,'sink_count':2,'target':check.TARGET,'terms':[]}
        multiplied=dict(base,multiplier='tail_sum')
        monomial=[1,1,0,0,0,0,0,0,0,0,1,1]
        outer=[1]+[0]*11
        with_square=deepcopy(multiplied)
        with_square['terms']=[['1',[outer,[[monomial,'1']]]]]
        def run(name,certificate,directory,must_reject):
            path=Path(temp)/directory/'certificate_0.json'
            path.write_text(json.dumps(certificate))
            try:check_extended.check_one((temp,0,0,(0,0,0,0,0),directory))
            except (ValueError,TypeError,ZeroDivisionError,IndexError):
                require(must_reject,'Unexpected rejection: '+name)
                tests.append({'test':name,'result':'rejected as required'})
            else:
                require(not must_reject,'Failed to reject: '+name)
                tests.append({'test':name,'result':'accepted as required'})
        run('ordinary schema preserved',base,'two-sink-cubic',False)
        run('valid tail-sum coefficientwise target',multiplied,'tail-sum-cubic',False)
        run('valid homogeneous degree-nine monomial square',with_square,'tail-sum-cubic',False)
        run('tail-sum directory requires explicit multiplier',base,'tail-sum-cubic',True)
        run('ordinary directory rejects multiplier certificate',multiplied,'two-sink-cubic',True)
        for value in ['head_sum','tail_product',None,1,True,{},['tail_sum']]:
            c=deepcopy(multiplied);c['multiplier']=value
            run('unsupported multiplier '+repr(value),c,'tail-sum-cubic',True)
        c=deepcopy(with_square);c['terms'][0][1][0]=[0]*12
        run('degree-eight square rejected in degree-nine target',c,'tail-sum-cubic',True)
        c=deepcopy(multiplied);c['target']='(sum core tails)*(gamma2^2-3gamma1gamma3)'
        run('legacy descriptive target is not canonical production schema',c,'tail-sum-cubic',True)
        (Path(temp)/'two-sink-cubic/certificate_0.json').write_text(json.dumps(base))
        (Path(temp)/'tail-sum-cubic/certificate_0.json').write_text(json.dumps(multiplied))
        try:check_extended.discover_certificate_locations(temp)
        except ValueError:tests.append({'test':'duplicate ID across certificate directories','result':'rejected as required'})
        else:raise ValueError('Duplicate proof-directory ID was accepted')
    # Selected ordinary certificates, including hard repairs, must preserve
    # every prior per-certificate result under the extended parser.
    regression_ids=[0,1,42,66,72,90,93,191,193,195,206,207]
    regression=[]
    for ident in regression_ids:
        if not (source/'two-sink-cubic'/f'certificate_{ident}.json').exists():continue
        job=(str(source),ident,*cores[ident])
        require(check_extended.check_one(job)==check_fast.check_one(job),f'Ordinary regression mismatch: {ident}')
        regression.append(ident)
    require(canonical_path.read_bytes()==canonical_raw,'Canonical 762 changed during tests')
    receipt={'status':'PASS','canonical_762_record':record,'canonical_762_regression_counts_verified':True,
             'schema_tests':tests,'ordinary_regression_ids':regression,
             'ordinary_regression_records_identical':True,
             'only_new_multiplier':'tail_sum','only_new_total_degree':9,
             'directory_contract':'untagged degree 8 in two-sink-cubic; tagged tail_sum degree 9 in tail-sum-cubic; duplicate IDs rejected',
             'boundary_inference':'U=sum of five nonnegative core tail activities; divide if U>0; if U=0 then all positive-rank gamma coefficients are zero',
             'original_checker_sha256':hashlib.sha256(Path(check.__file__).read_bytes()).hexdigest(),
             'optimized_checker_sha256':hashlib.sha256(Path(check_fast.__file__).read_bytes()).hexdigest(),
             'extended_checker_sha256':hashlib.sha256(Path(check_extended.__file__).read_bytes()).hexdigest(),
             'selftest_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'producer_code_imported_or_executed':False,'seconds':round(time.time()-started,3)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
