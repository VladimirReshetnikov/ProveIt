#!/usr/bin/env python3
"""Rebuild all selected polynomial circuits from their frozen pivots."""
from pathlib import Path
import argparse,json,hashlib
import producer

ROOT=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Compare reconstructed bytes with delivered equations')
    parser.add_argument('--output',type=Path,help='Write reconstructed equation files into this directory')
    args=parser.parse_args()
    if not args.check and args.output is None:args.check=True
    if args.output:args.output.mkdir(parents=True,exist_ok=True)
    reports=[]
    for path in sorted((ROOT/'certificates').glob('*.json')):
        profile=json.loads(path.read_text());base=ROOT/profile['base_file']
        if hashlib.sha256(base.read_bytes()).hexdigest()!=profile['base_sha256']:
            raise ValueError('Base circuit hash differs')
        program=producer.build(profile,base)
        name='integer{variables}_degree{degree}.json'.format(**program['metrics'])
        encoded=json.dumps(program,sort_keys=True,separators=(',',':'))+'\n'
        if args.check and encoded!=(ROOT/'equations'/name).read_text():
            raise ValueError('Reconstruction differs: '+name)
        if args.output:(args.output/name).write_text(encoded)
        reports.append({'file':name,'base_file':base.name,**program['metrics']})
    if args.output:(args.output/'RESULTS.json').write_text(json.dumps(reports,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS','byte_exact_check':args.check,'programs':reports},sort_keys=True))
if __name__=='__main__':main()
