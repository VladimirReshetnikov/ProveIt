#!/usr/bin/env python3
"""Read-only finite verification. Uses Python 3.10+ and its standard library."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from copy import deepcopy

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from arithmetic import audit as arithmetic_audit
from coefficients import old_decode,new_decode,tiles,constants,parse62,EXPECTED,ALPHABET
from build import construct
from check_carrier65_independent import audit as independent_audit

def need(condition,message):
    if not condition:raise ValueError(message)

def literal(path):
    return ''.join(re.findall(r'^([A-Za-z0-9]+)\\par$',path.read_text(),re.M))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--skip-manifest',action='store_true',
                        help='Permit intentional PDF rebuilds; arithmetic identities remain checked')
    args=parser.parse_args()
    manifest_count=0
    if (ROOT/'SHA256SUMS').exists() and not args.skip_manifest:
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            digest,relative=line.split('  ',1)
            need(hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()==digest,
                 'Release file differs: '+relative)
            manifest_count+=1
    pins=json.loads((ROOT/'sources/SOURCE_PINS.json').read_text())
    for item in pins['files']:
        path=ROOT/'sources'/item['local']
        if not path.exists():path=ROOT/'licenses'/item['local']
        need(hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],
             'Pinned source differs: '+item['local'])
    old_literal=literal(ROOT/'sources/CURRENT_P66.tex')
    new_literal=literal(ROOT/'equation.tex')
    need(new_literal==(ROOT/'equation/SEED.txt').read_text().strip(),'Printed numeral differs')
    need(len(old_literal)==436 and len(new_literal)==399,'Numeral lengths')
    actions_old,actions_new=old_decode(old_literal),new_decode(new_literal)
    need(actions_old==actions_new,'Action-stream identity')
    need([j for j,a in enumerate(actions_new) if a[0]==215]==[125],'Early halt')
    tiles_old,tiles_new=tiles(actions_old),tiles(actions_new)
    need(tiles_old==tiles_new,'All 942 indexed tiles')
    ports=constants(tiles_new)
    need(ports==constants(tiles_old),'Whole coefficient identity')
    need(ports['beta']>=31 and ports['K']>0 and
         0<ports['MC']<ports['beta']<ports['MF_source']<2*ports['beta'],
         'Scalar interface')
    port_record={}
    for name,value in ports.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'big')
        digest=hashlib.sha256(raw).hexdigest()
        need(digest==EXPECTED[name],'Pinned coefficient hash '+name)
        need(raw==(ROOT/'equation/coefficients'/(name+'.bin')).read_bytes(),
             'Coefficient byte file '+name)
        port_record[name]={'bits':value.bit_length(),'bytes':len(raw),'sha256':digest}
    rebuilt=construct()
    for name,raw in rebuilt.items():
        need(raw==(ROOT/'equation'/name).read_bytes(),'Rebuilt artifact differs: '+name)
    graph_path=ROOT/'equation/carrier65.json'
    graph=json.loads(graph_path.read_text())
    parent=json.loads((ROOT/'sources/parent_polynomial.json').read_text())
    producer=arithmetic_audit(graph,parent)
    independent=independent_audit(graph_path)
    seed_check=json.loads(subprocess.check_output(
        [sys.executable,str(ROOT/'code/check_seed_independent.py')],text=True))
    negative_controls=[]
    for i in [0,199,398]:
        bad=new_literal[:i]+ALPHABET[(ALPHABET.index(new_literal[i])+1)%62]+new_literal[i+1:]
        need(new_decode(bad)!=actions_old,'Changed seed escaped control')
        negative_controls.append('seed symbol '+str(i))
    for label,change in [
        ('wrong trace sign',lambda g: next(r for r in g['source'] if r[0]=='tau').__setitem__(1,'+')),
        ('missing product factor',lambda g: next(r for r in g['source'] if r[0]=='product3').__setitem__(2,1)),
        ('wrong witness domain',lambda g:g.__setitem__('witness_domain','unrestricted integers')),
    ]:
        bad=deepcopy(graph);change(bad)
        with tempfile.TemporaryDirectory() as t:
            f=Path(t)/'bad.json';f.write_text(json.dumps(bad))
            try:independent_audit(f)
            except (ValueError,KeyError):negative_controls.append(label)
            else:raise ValueError('Corruption escaped: '+label)
    companions={}
    for name,n,ops,degree in [('natural14',14,79,150),('integer42',42,163,300)]:
        g=json.loads((ROOT/'equation'/(name+'.json')).read_text())
        need(len(g['witnesses'])==n and len(g['source'])==ops and g['exact_degree']==degree,
             'Companion literal metric')
        companions[name]={'variables':n,'operations':ops,'exact_degree':degree,
                          'operation_counts':g['operation_counts']}
    result={'status':'PASS','source_commit':pins['commit'],
            'manifest_files_checked':manifest_count,
            'source_files_checked':len(pins['files']),
            'byte_identical_reconstructions':len(rebuilt),
            'new_arithmetic':producer,'independent_arithmetic':independent,
            'independent_seed':seed_check,'fixed_coefficients':port_record,
            'domain_companions':companions,'negative_controls':negative_controls,
            'scope':'Finite formula, degree, integer coefficients, domains, source identity and reconstruction checks. The unbounded proof is ordinary mathematics composed with the pinned P66/refutation calibration.'}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
