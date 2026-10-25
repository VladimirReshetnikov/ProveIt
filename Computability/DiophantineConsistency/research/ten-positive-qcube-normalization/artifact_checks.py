#!/usr/bin/env python3
"""Actual malformed-packet controls against the separately pinned exact checker."""
import argparse,importlib.util,io,json,sys,tempfile
from contextlib import redirect_stdout
from hashlib import sha256
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PINS={'README.md': 'd63599cb0b9c31c69adb4ab3c76e04481024e2646b46edb1417878fab828fb7a', 'PROOF.md': '452f4e170e84886af9ffaf952f603fbca2447dedb3d85c3065eafc4eecb86294', 'SOURCE_PINS.json': '8ad1ad79e08f9bcb55506132d4c88c03d09c4ebc107d6e9a976fb3146b9f280a', 'build.py': 'a2ec64942763671d6a2c11dd317d16c3ebd6ed4f494986b795bd530311f30425', 'check.py': 'a5c5078acc6f16bfd37038d16445ff02bca2ffb6ca9f148e29c9d692e3e906a0'}

def need(ok,why):
    if not ok:raise ValueError(why)
def digest(blob):return sha256(blob).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    need(set(PINS)=={'README.md','PROOF.md','SOURCE_PINS.json','build.py','check.py'},'whole independently pinned author core')
    for n,h in PINS.items():need(digest((HERE/n).read_bytes())==h,'whole reviewed author core '+n)
    payload={str(p.relative_to(HERE)):p.read_bytes() for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'};payload['nested/MANIFEST.json']=b'{}\n'
    spec=importlib.util.spec_from_file_location('qcube_exact_checker',HERE/'check.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    rejected=[]
    with tempfile.TemporaryDirectory(prefix='qcube-actual-artifacts-') as directory:
        base=Path(directory);folder=base/'packet';receipt=base/'receipt.json';checker.HERE=folder;checker.ROOT=ROOT
        def reset(sealed=False):
            if folder.exists():
                for p in sorted(folder.rglob('*'),key=lambda p:len(p.parts),reverse=True):p.unlink() if p.is_file() else p.rmdir()
            folder.mkdir(exist_ok=True)
            for n,b in payload.items():
                target=folder/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
            if sealed:(folder/'MANIFEST.json').write_text(json.dumps(dict(files={n:digest(b) for n,b in payload.items()}),sort_keys=True)+'\n')
            if receipt.exists():receipt.unlink()
        def replay():
            previous=sys.argv;sys.argv=['exact-check.py','--output',str(receipt)]
            try:
                with redirect_stdout(io.StringIO()):checker.main()
            finally:sys.argv=previous
        def edit(n,action):
            p=folder/n;data=json.loads(p.read_bytes());action(data);p.write_text(json.dumps(data,sort_keys=True)+'\n')
        def row(d,n):return next(r for r in d['source'] if r[0]==n)
        def reject(n,mutation,sealed=False):
            reset(sealed);mutation()
            try:replay()
            except (ValueError,KeyError,TypeError,IndexError,OSError,EOFError) as e:rejected.append(dict(name=n,exception=type(e).__name__,reason=str(e)))
            else:raise ValueError('actual checker accepted malformed whole artifact '+n)
        reset();replay();same=receipt.read_bytes();replay();need(receipt.read_bytes()==same,'idempotent same receipt')
        receipt.write_bytes(b'preserve a differing receipt\n')
        try:replay()
        except ValueError:need(receipt.read_bytes()==b'preserve a differing receipt\n','differing receipt preserved')
        else:raise ValueError('differing receipt overwritten')
        reset(True);replay();need(json.loads(receipt.read_bytes())['status']=='PASS','complete closed positive packet with nested manifest')
        for label,node,col,value in [('wrong normalized sign','Znum',1,'+'),('old residual minus','brk',1,'-'),('old P factor','P1mu2',2,'q3'),('lost e factor','P1e',2,1),('old Y fraction','mu2inner',3,'Y'),('wrong substitution power','Y',2,'q2'),('omitted n','nV',2,1),('old weight','LBt',2,'k'),('lost coprime factor','Dg',2,1),('wrong norm sign','N',1,'+'),('wrong denominator','Mtot',2,'mu2')]:
            reject(label,lambda nd=node,c=col,v=value:edit('zero86.json',lambda d:row(d,nd).__setitem__(c,v)))
        for key,value in [('domain','unrestricted integers'),('exact_degree',478),('operations',85),('name','same_specialized_polynomial')]:reject('wrong metadata '+key,lambda k=key,v=value:edit('zero86.json',lambda d:d.update({k:v})))
        reject('wrong quantified input',lambda:edit('zero86.json',lambda d:d['witnesses'].__setitem__(6,'Y')))
        reject('dead gate hidden from count',lambda:edit('zero86.json',lambda d:d['source'].append(['dead','+',1,1])))
        reject('missing complete row map',lambda:edit('CUTS.json',lambda d:d['complete_parent_to_new_rows'].pop()))
        reject('wrong cleared q power',lambda:edit('CUTS.json',lambda d:d['clearing'].update(N_old='q^4*N_new')))
        reject('wrong shifted-domain map',lambda:edit('CUTS.json',lambda d:d['coordinate_map'].update(n_old='n_new+s')))
        reject('changed whole copied parent',lambda:edit('parents/zero89.json',lambda d:row(d,'P1').__setitem__(2,'q2')))
        reject('changed inherited complete proof',lambda:(folder/'parents/PROOF.md').write_text('assume n-s positive\n'))
        reject('changed nested parent seal',lambda:(folder/'parents/MANIFEST.json').write_text('{}\n'))
        old=json.loads(payload['zero86.json'])['coefficient_binding']['ports']['K0']
        reject('splice BFS K into indexed metadata',lambda:edit('INDEXED_BINDING.json',lambda d:d['ports']['K0'].update(old)))
        reject('splice BFS wholeK into indexed payload',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').write_bytes(payload['coefficients/compact44_bfs/K.bin.gz']))
        reject('damaged whole beta',lambda:(folder/'coefficients/compact44_bfs/beta.bin.gz').write_bytes(b'not a numeral'))
        first=next(iter(json.loads(payload['SOURCE_PINS.json'])['files']))
        reject('missing source pin',lambda:edit('SOURCE_PINS.json',lambda d:d['files'].pop(first)))
        reject('changed whole immutable pin',lambda:edit('SOURCE_PINS.json',lambda d:d['files'].update({first:'0'*64})))
        reject('missing closed calibration',lambda:edit('SOURCE_PINS.json',lambda d:d['closed_dependencies'].pop()))
        reject('unlisted closed file',lambda:(folder/'unlisted.txt').write_text('unlisted'),True)
        reject('closed missing nested manifest',lambda:edit('MANIFEST.json',lambda d:d['files'].pop('nested/MANIFEST.json')),True)
        reject('closed changed ordinary theorem',lambda:(folder/'PROOF.md').write_text('assert positive reverse shear\n'),True)
        reject('closed missing full coefficient',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').unlink(),True)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),reviewed_core=PINS,rejected_actual_artifacts=rejected,rejected_count=len(rejected),positive_controls=['complete unsealed packet','complete sealed packet with nested manifest','idempotent same receipt','differing receipt preserved'],actual_author_checker_imported=True,builder_or_parent_or_incoming_code_executed=False,unbounded_proof_replaced_by_controls=False,immutable_sources_modified=False,audit_sha256=digest(Path(__file__).read_bytes()))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed output overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),rejected_actual_artifacts=len(rejected),positive_controls=4),sort_keys=True))
if __name__=='__main__':main()
