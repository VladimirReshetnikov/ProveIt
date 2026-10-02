#!/usr/bin/env python3
"""Extended exact hybrid audit of five-core/two-sink cubic inequality.

Run: python hybrid.py SOURCE [--partial] [--workers N] [--output RECEIPT]
Full mode requires complete union coverage by freshly verified structural
maps, preorder maps, and exact SOS certificates. Partial mode never claims
that union is complete. Only the independent check.py and structural.py
modules in this directory are imported, never producer code.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from collections import Counter
import argparse
import hashlib
import json
import re
import time
import check_extended as check
import structural

R=Path(__file__).resolve().parent


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('--partial',action='store_true')
    parser.add_argument('--workers',type=int,default=4)
    parser.add_argument('--output',type=Path,default=R/'hybrid-receipt.json')
    args=parser.parse_args()
    check.require(args.workers>=1,'Worker count must be positive')
    started=time.time()
    cores,catalog_hash=check.read_catalog(args.source/'cores.txt')
    print('Rechecking structural covers, side matroids, HPP maps, and preorders',flush=True)
    structural_ids,structural_receipt,structural_records=structural.verify_structural(args.source,cores)
    preorder_ids,preorder_receipt,preorder_records=structural.verify_preorders(args.source,cores)
    locations=check.discover_certificate_locations(args.source)
    ids=sorted(locations)
    union=structural_ids|preorder_ids|set(ids)
    missing=sorted(set(range(len(cores)))-union)
    if not args.partial:
        check.require(not missing,f'Hybrid proof incomplete: {len(missing)} classes lack any proposed proof')
    print(f'Checking {len(ids)} exact certificates; proposed union {len(union)}/{len(cores)}',flush=True)
    records=[]
    jobs=((str(args.source),ident,cores[ident][0],cores[ident][1],locations[ident]) for ident in ids)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for record in pool.map(check.check_one,jobs,chunksize=4):
            records.append(record)
            if len(records)%200==0:
                print(f'Checked {len(records)} SOS certificates in {time.time()-started:.2f}s',flush=True)
    print('Checking literal/Hall support agreement and orbit coverage for every class',flush=True)
    support_counts=Counter()
    for code,rows in cores:
        gamma=check.construct_gammas(code,rows)
        for k,g in enumerate(gamma):
            support_counts[k]+=len(g)
    coverage=check.check_coverage(cores)
    check.require(hashlib.sha256((args.source/'cores.txt').read_bytes()).hexdigest()==catalog_hash,
                  'Catalog changed during audit')
    check.require(hashlib.sha256((args.source/'structural-9608.json').read_bytes()).hexdigest()==structural_receipt['structural_source_sha256'],
                  'Structural maps changed during audit')
    if preorder_receipt['present']:
        check.require(hashlib.sha256((args.source/'preorder-coverage.json').read_bytes()).hexdigest()==preorder_receipt['source_sha256'],
                      'Preorder maps changed during audit')
    for record in records:
        path=args.source/locations[record['id']]/f"certificate_{record['id']}.json"
        check.require(hashlib.sha256(path.read_bytes()).hexdigest()==record['certificate_sha256'],
                      'Certificate changed during audit: '+path.name)
    structural_methods={r['id']:r['method'] for r in structural_records}
    certificate_methods={r['id']:('tail_sum_rational_square_certificate' if r.get('multiplier')=='tail_sum' else 'exact_rational_square_certificate') for r in records}
    ledger=[]
    for ident in range(len(cores)):
        if ident in structural_ids:
            ledger.append({'id':ident,'selected_method':structural_methods[ident]})
        elif ident in preorder_ids:
            ledger.append({'id':ident,'selected_method':'previous_weighted_preorder_degree_three_theorem'})
        elif ident in ids:
            ledger.append({'id':ident,'selected_method':certificate_methods[ident]})
        else:
            ledger.append({'id':ident,'selected_method':'MISSING'})
    selected_counts=Counter(x['selected_method'] for x in ledger)
    manifest_hash=hashlib.sha256('\n'.join(f"{r['id']}:{r['certificate_sha256']}" for r in records).encode()).hexdigest()
    lengths=Counter()
    for record in records:
        lengths.update(record['square_length_histogram'])
    receipt={
        'status':'PARTIAL_PASS' if args.partial else 'PASS',
        'complete_hybrid_domain_verified':not args.partial,
        'target':check.TARGET,'variables':check.VARIABLES,'target_homogeneous_degree':8,
        'certificate_homogeneous_degrees':[8,9],
        'multiplier_counts':dict(Counter(r.get('multiplier','none') for r in records)),
        'tail_sum_boundary_argument':'U>0 permits division; U=0 forces all positive-rank support coefficients to vanish',
        'arithmetic':'Exact integers and fractions.Fraction only',
        'standard_library_only':True,'producer_code_imported_or_executed':False,
        'covered_class_count':len(union),'missing_class_count':len(missing),
        'missing_class_ids':missing,'expected_class_count':len(cores),
        'selected_disjoint_ledger_counts':dict(selected_counts),
        'all_available_certificate_count':len(records),
        'certificate_overlap_with_structural_or_preorder_count':len(set(ids)&(structural_ids|preorder_ids)),
        'positive_rational_square_count':sum(r['square_count'] for r in records),
        'square_length_histogram':dict(sorted(lengths.items())),
        'all_exact_remainders_coefficientwise_nonnegative':True,
        'positive_remainder_term_count':sum(r['positive_remainder_term_count'] for r in records),
        'all_9608_literal_and_hall_support_polynomials_equal':True,
        'support_counts_summed_over_all_representatives':dict(sorted(support_counts.items())),
        'structural':structural_receipt,'preorder':preorder_receipt,
        'coverage':coverage,'checked_source_files_unchanged_during_run':True,
        'catalog_sha256':catalog_hash,'certificate_manifest_sha256':manifest_hash,
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'polynomial_checker_sha256':hashlib.sha256(Path(check.__file__).read_bytes()).hexdigest(),
        'structural_checker_sha256':hashlib.sha256(Path(structural.__file__).read_bytes()).hexdigest(),
        'structural_support_checker_sha256':hashlib.sha256(Path(structural.check.__file__).read_bytes()).hexdigest(),
        'seconds':round(time.time()-started,3),
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    args.output.with_name(args.output.stem+'-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
    args.output.with_name(args.output.stem+'-certificate-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
    args.output.with_name(args.output.stem+'-structural-records.json').write_text(json.dumps(
        {'structural':structural_records,'preorders':preorder_records},indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='missing_class_ids'},indent=2),flush=True)


if __name__=='__main__':
    main()
