#!/usr/bin/env python3
"""Rebuild the recognized-format census from an exact pinned ProveIt checkout.

This optional larger operation needs the complete PA tree and six incoming
ZIPs at the source snapshot. The offline novelty replay needs no checkout.
No source file is changed and no source generator is executed.
"""
from pathlib import Path
import argparse,gzip,json,subprocess,sys,tempfile
from schema_parser import scan

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();here=Path(__file__).resolve().parent
    expected=json.loads((here/'base_census_summary.json').read_text())
    args.output.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='pa194-census-manifest-') as tmp:
        manifest=Path(tmp)/'manifest.json'
        manifest.write_bytes(gzip.decompress((here/'scope_manifest.json.gz').read_bytes()))
        scan(args.source.resolve(),args.output.resolve(),manifest)
    actual=json.loads((args.output/'summary.json').read_text())
    for key,value in expected.items():
        if key!='elapsed_seconds' and actual[key]!=value:
            raise ValueError('Census differs in '+key+': '+repr(actual[key])+' versus '+repr(value))
    subprocess.run([sys.executable,'-B',str(here/'supplement_json_census.py'),
                    '--source',str(args.source.resolve()),
                    '--base-census',str((args.output/'census.json').resolve()),
                    '--output',str((args.output/'json_coverage').resolve())],check=True)
    supplemental=json.loads((args.output/'json_coverage/summary.json').read_text())
    expected_supplement=json.loads((here/'json_coverage/summary.json').read_text())
    for key,value in expected_supplement.items():
        if key!='elapsed_seconds' and supplemental[key]!=value:
            raise ValueError('Supplemental census differs in '+key)
    for filename in ('occurrences.json','identities.json'):
        if json.loads((args.output/'json_coverage'/filename).read_text())!=json.loads((here/'json_coverage'/filename).read_text()):
            raise ValueError('Supplemental census differs in '+filename)
    actual['table_occurrences']+=supplemental['additional193_194_occurrences']
    actual['normalized_tables']+=supplemental['additional_normalized_identities']
    actual['unknown_start_occurrences']+=supplemental['additional193_194_occurrences']
    combined=json.loads((here/'census_summary.json').read_text())
    for key,value in actual.items():
        if key!='elapsed_seconds' and combined[key]!=value:
            raise ValueError('Combined census differs in '+key)
    (args.output/'combined_summary.json').write_text(json.dumps(combined,indent=2)+'\n')
    print('Pinned combined census reproduced: 7,342 occurrences, 1,381 normalized tables, 548 spanning 194-control graph classes.')

if __name__=='__main__':main()
