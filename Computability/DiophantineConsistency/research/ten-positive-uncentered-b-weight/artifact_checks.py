#!/usr/bin/env python3
"""Exercise the exact author checker on private complete malformed packets."""
import argparse
from contextlib import redirect_stdout
from copy import deepcopy
from hashlib import sha256
import importlib.util,io,json,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PINS={'README.md': '529a70d2e1720010e591c1f60dddd953d9184ddf1395259e552b2d1f0bfa36dc', 'PROOF.md': 'd769bc6b43fe34cc9c0d6d14c0f4a5a9baa12c4bfa95ec8a4bb668854c5716b5', 'SOURCE_PINS.json': '222e18b72643383dd9d7a3978f7573379774b4187f7ead79f6da50a722af747e', 'build.py': '25c64a384bc7ae95af522dae98d6892105f79cd20de15344f25ec7406c149579', 'check.py': '20b0340a1090c7d38b07b69c029124ee22e375b215d24debc76343fd2a4aa5d2'}
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(blob):return sha256(blob).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    need(set(PINS)=={'README.md','PROOF.md','SOURCE_PINS.json','build.py','check.py'},'whole reviewed author core pin inventory')
    for name,h in PINS.items():need(digest((HERE/name).read_bytes())==h,'whole reviewed author core '+name)
    payload={str(p.relative_to(HERE)):p.read_bytes() for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'};payload['nested/MANIFEST.json']=b'{}\n'
    spec=importlib.util.spec_from_file_location('reviewed_uncentered_checker',HERE/'check.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    rejected=[]
    with tempfile.TemporaryDirectory(prefix='uncentered-b-artifacts-') as directory:
        base=Path(directory);folder=base/'packet';receipt=base/'receipt.json';checker.HERE=folder;checker.ROOT=ROOT
        def reset(sealed=False):
            if folder.exists():
                for p in sorted(folder.rglob('*'),key=lambda p:len(p.parts),reverse=True):p.unlink() if p.is_file() else p.rmdir()
            folder.mkdir(exist_ok=True)
            for name,blob in payload.items():
                target=folder/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(blob)
            if sealed:(folder/'MANIFEST.json').write_text(json.dumps(dict(files={n:digest(b) for n,b in payload.items()}),sort_keys=True)+'\n')
            if receipt.exists():receipt.unlink()
        def replay():
            old=sys.argv;sys.argv=['reviewed-check.py','--output',str(receipt)]
            try:
                with redirect_stdout(io.StringIO()):checker.main()
            finally:sys.argv=old
        def edit(name,action):
            path=folder/name;data=json.loads(path.read_bytes());action(data);path.write_text(json.dumps(data,sort_keys=True)+'\n')
        def row(data,name):return next(r for r in data['source'] if r[0]==name)
        def reject(name,mutation,sealed=False):
            reset(sealed);mutation()
            try:replay()
            except (ValueError,KeyError,TypeError,IndexError,OSError,EOFError) as error:rejected.append(dict(name=name,exception=type(error).__name__,reason=str(error)))
            else:raise ValueError('actual checker accepted malformed whole artifact '+name)
        reset();replay();normal=receipt.read_bytes();replay();need(receipt.read_bytes()==normal,'idempotent same-receipt write')
        receipt.write_bytes(b'preserve a differing receipt\n')
        try:replay()
        except ValueError:need(receipt.read_bytes()==b'preserve a differing receipt\n','different output preserved')
        else:raise ValueError('differing receipt overwritten')
        reset(True);replay();need(json.loads(receipt.read_bytes())['status']=='PASS','whole closed positive control including nested manifest')
        for name in ['zero89.json','direct95.json']:
            reject(name+':wrong norm sign',lambda n=name:edit(n,lambda d:row(d,'N').__setitem__(1,'+')))
            reject(name+':omit first-square factor',lambda n=name:edit(n,lambda d:row(d,'Dg').__setitem__(2,1)))
            reject(name+':old centered consumer',lambda n=name:edit(n,lambda d:row(d,'center').__setitem__(2,'nVCg')))
            reject(name+':revert weight',lambda n=name:edit(n,lambda d:row(d,'LBt').__setitem__(2,'k')))
            reject(name+':change quantified domain',lambda n=name:edit(n,lambda d:d.update(domain='unrestricted integers')))
            reject(name+':wrong exact degree',lambda n=name:edit(n,lambda d:d.update(exact_degree=1)))
        reject('direct missing q in P',lambda:edit('direct95.json',lambda d:row(d,'P1').__setitem__(2,'q3')))
        reject('drop full old-row map',lambda:edit('CUTS.json',lambda d:d['saturated_upper']['complete_parent_to_new_rows'].pop()))
        reject('hide deleted center gate',lambda:edit('CUTS.json',lambda d:d['saturated_sharp']['deleted_rows'].pop()))
        reject('change copied complete parent',lambda:edit('parents/saturated_upper.json',lambda d:row(d,'Cg').__setitem__(2,'U')))
        reject('change copied old proof',lambda:(folder/'parents/PROOF.md').write_text('assume transport positive\n'))
        reject('change copied nested seal',lambda:(folder/'parents/MANIFEST.json').write_text('{}\n'))
        old=json.loads(payload['zero89.json'])['coefficient_binding']['ports']['K0']
        reject('splice only oldK into indexed binding',lambda:edit('INDEXED_BINDING.json',lambda d:d['ports']['K0'].update(old)))
        reject('substitute old payload for indexedK',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').write_bytes(payload['coefficients/compact44_bfs/K.bin.gz']))
        reject('change entire beta payload',lambda:(folder/'coefficients/compact44_bfs/beta.bin.gz').write_bytes(b'not a coefficient'))
        first=next(iter(json.loads(payload['SOURCE_PINS.json'])['files']))
        reject('drop immutable dependency pin',lambda:edit('SOURCE_PINS.json',lambda d:d['files'].pop(first)))
        reject('drop closed source contract',lambda:edit('SOURCE_PINS.json',lambda d:d['closed_dependencies'].pop()))
        reject('alter immutable dependency hash',lambda:edit('SOURCE_PINS.json',lambda d:d['files'].update({first:'0'*64})))
        reject('closed inventory omits nested manifest',lambda:edit('MANIFEST.json',lambda d:d['files'].pop('nested/MANIFEST.json')),True)
        reject('closed inventory rejects unlisted file',lambda:(folder/'unlisted.json').write_text('{}\n'),True)
        reject('closed inventory authenticates new ordinary proof',lambda:(folder/'PROOF.md').write_text('assert all radicals positive\n'),True)
        reject('closed inventory rejects missing full numeral',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').unlink(),True)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),reviewed_core=PINS,positive_controls=['complete unsealed packet','complete sealed packet including nested manifest','idempotent same receipt','different receipt preserved'],rejected_actual_artifacts=rejected,rejected_count=len(rejected),author_checker_imported=True,builder_or_parent_or_incoming_code_executed=False,immutable_sources_modified=False,unbounded_proof_replaced_by_controls=False,audit_sha256=digest(Path(__file__).read_bytes()))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),rejected_actual_artifacts=len(rejected),positive_controls=4),sort_keys=True))
if __name__=='__main__':main()
