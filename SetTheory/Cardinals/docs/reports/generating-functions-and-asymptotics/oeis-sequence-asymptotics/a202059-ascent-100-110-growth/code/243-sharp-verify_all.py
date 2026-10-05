#!/usr/bin/env python3
"""Reproduce deterministic Report243 receipts in a NEW external directory.

Run every mathematical and guard test normally and under -O, compare bytes,
then emit CSV views. No network, external packages or numerical fitting.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess
from common import (ROOT, REPORT_NUMBER, child_environment, emit,
                    new_file_path, python_command, require)

SCRIPTS = (('exact_counts.py','count_receipt.json'),
           ('upper_bound.py','upper_bound_receipt.json'),
           ('positive_rows.py','positive_rows_receipt.json'),
           ('guard_tests.py','guard_receipt.json'))


def csv_bytes(rows,fields):
    stream = io.StringIO(newline='')
    writer = csv.DictWriter(stream,fieldnames=fields,lineterminator='\n',extrasaction='ignore')
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue().encode('ascii')


def write_new(path,payload):
    with path.open('xb') as handle:
        handle.write(payload)


def reproduce(output_dir,compare_reference=True):
    require(isinstance(compare_reference,bool),'comparison selector must be Boolean')
    destination = new_file_path(output_dir)
    destination.mkdir(exist_ok=False)
    results,hashes = {},{}
    for script,receipt in SCRIPTS:
        payloads = []
        for optimized in (0,1):
            result = subprocess.run(python_command(optimized)+['-E',str(ROOT/'code'/script)],
                                    env=child_environment(),capture_output=True,check=False,timeout=300)
            require(result.returncode==0,script+' failed: '+result.stderr.decode('utf-8',errors='replace')[:4000])
            require(len(result.stdout)<=2_000_000,'receipt exceeds output budget')
            data = json.loads(result.stdout)
            require(data.get('status')=='PASS',script+' did not pass')
            payloads.append(result.stdout)
        require(payloads[0]==payloads[1],script+' normal/-O receipts differ')
        reference = ROOT/'code'/receipt
        if compare_reference:
            require(reference.is_file() and reference.read_bytes()==payloads[0],receipt+' differs from checked-in reference')
        write_new(destination/receipt,payloads[0])
        results[receipt] = json.loads(payloads[0])
        hashes[receipt] = hashlib.sha256(payloads[0]).hexdigest()
    counts = results['count_receipt.json']['literal_raw_cross_checks']
    upper = results['upper_bound_receipt.json']['rows']
    positive = results['positive_rows_receipt.json']
    markov = [{key:row[key] for key in ('r','q','M','Q','nontrivial_cutoff','empty_expectation','eligible_fraction')}
              for row in positive['nontrivial_markov_checks']]
    all_lengths = positive['all_length_examples']
    exports = {
        'counts.csv':csv_bytes(counts,['n','all_ascent_sequences','avoid_100','avoid_110','avoid_000_100','avoid_000_100_110']),
        'upper_bounds.csv':csv_bytes(upper,['n','pattern','count','skeletons','run_candidate_checks','finite_upper_bound']),
        'positive_rows.csv':csv_bytes(positive['exhaustive']['rows'],['n','r','q','T','Q','eligible_arrays','empty_expectation',
            'repaired_arrays','distinct_words_000_100','distinct_common_words','max_repair_fiber','max_composition_fiber',
            'max_padding_fiber','max_common_padding_fiber','padded_words_000_100','padded_common_words','lower_denominator']),
        'markov.csv':csv_bytes(markov,['r','q','M','Q','nontrivial_cutoff','empty_expectation','eligible_fraction']),
        'all_lengths.csv':csv_bytes(all_lengths,['target','class','n','r','q','M','Q','repair_and_seed_target','extra_padding',
            'sample_original_empty_rows','sample_pre_padding_length','sample_final_length','sample_word_sha256'])}
    for filename,payload in exports.items():
        if compare_reference:
            reference = ROOT/'code'/filename
            require(reference.is_file() and reference.read_bytes()==payload,filename+' differs from reference')
        write_new(destination/filename,payload)
        hashes[filename] = hashlib.sha256(payload).hexdigest()
    summary = {'status':'PASS','report_number':REPORT_NUMBER,'normal_optimized_byte_identity':True,
               'files_sha256':hashes,'scope':'Bounded exact reproduction only; proof is in the article.'}
    emit(summary,str(destination/'reproduction_receipt.json'))
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',required=True)
    parser.add_argument('--no-reference-comparison',action='store_true',
                        help='Generate a fresh reference set; never modifies the source directory')
    args = parser.parse_args()
    emit(reproduce(args.output_dir,not args.no_reference_comparison))


if __name__ == '__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError,subprocess.TimeoutExpired) as exc:
        raise SystemExit(str(exc))
