#!/usr/bin/env python3
"""Full private packet mutations for the exact direct-carrier checker."""
import argparse
from contextlib import redirect_stdout
from hashlib import sha256
import importlib.util,io,json,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PINS={'README.md': '8a9001bc0f1120649b45f359a0a22f12f4de89972855578738e0680dc3f35f89', 'PROOF.md': '311e91a5d3dd37c8ef288ff29fb1baa7e609fdfb9dab44d600c38ba353323748', 'SOURCE_PINS.json': '8629fbfba23b0ed7dca63ab3a6a52089ae9b22ba18fc8a8c1503bd04add58b1e', 'build.py': '2bffbd69f9f20b6ecee544cbbba494d15e6da7865fae59530d2bc9b0967205b4', 'check.py': 'c984cb7b80d054a7292662aff38f9c56cfd0e96610ca36579f04159b4c17d495'}
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(b):return sha256(b).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();need(set(PINS)=={'README.md','PROOF.md','SOURCE_PINS.json','build.py','check.py'},'complete reviewed core pin inventory')
    for n,h in PINS.items():need(digest((HERE/n).read_bytes())==h,'whole reviewed author core '+n)
    payload={str(p.relative_to(HERE)):p.read_bytes() for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'};payload['nested/MANIFEST.json']=b'{}\n';spec=importlib.util.spec_from_file_location('reviewed_direct_cse_checker',HERE/'check.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker);rejected=[]
    with tempfile.TemporaryDirectory(prefix='direct-carrier-cse-artifacts-') as directory:
        folder=Path(directory)/'packet';receipt=Path(directory)/'receipt.json';checker.HERE=folder;checker.ROOT=ROOT
        def reset(sealed=False):
            if folder.exists():
                for p in sorted(folder.rglob('*'),key=lambda p:len(p.parts),reverse=True):p.unlink() if p.is_file() else p.rmdir()
            folder.mkdir(exist_ok=True)
            for n,b in payload.items():p=folder/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
            if sealed:(folder/'MANIFEST.json').write_text(json.dumps(dict(files={n:digest(b) for n,b in payload.items()}),sort_keys=True)+'\n')
            if receipt.exists():receipt.unlink()
        def replay():
            old=sys.argv;sys.argv=['reviewed-check.py','--output',str(receipt)]
            try:
                with redirect_stdout(io.StringIO()):checker.main()
            finally:sys.argv=old
        def edit(name,action):
            p=folder/name;d=json.loads(p.read_bytes());action(d);p.write_text(json.dumps(d,sort_keys=True)+'\n')
        def row(d,n):return next(r for r in d['source'] if r[0]==n)
        def reject(name,mutation,sealed=False):
            reset(sealed);mutation()
            try:replay()
            except (ValueError,KeyError,TypeError,IndexError,OSError,EOFError) as error:rejected.append(dict(name=name,exception=type(error).__name__,reason=str(error)))
            else:raise ValueError('accepted malformed whole artifact '+name)
        reset();replay();expected=receipt.read_bytes();replay();need(receipt.read_bytes()==expected,'same output is idempotent');receipt.write_bytes(b'preserve this differing receipt\n')
        try:replay()
        except ValueError:need(receipt.read_bytes()==b'preserve this differing receipt\n','different existing output preserved')
        else:raise ValueError('overwrote differing output')
        reset(True);replay();need(json.loads(receipt.read_bytes())['status']=='PASS','whole closed positive control including nested manifest')
        for entry in checker.ROUTES:
            target=entry[2];name=target+'.json'
            reject(target+':wrong shared factor',lambda n=name:edit(n,lambda d:row(d,'P1').__setitem__(3,'bJ')))
            reject(target+':reuse unavailable old coordinate',lambda n=name:edit(n,lambda d:row(d,'P1').__setitem__(2,'q4')))
            reject(target+':silently change another live gate',lambda n=name:edit(n,lambda d:row(d,'N').__setitem__(1,'+')))
            reject(target+':hide constant multiplication cost',lambda n=name:edit(n,lambda d:d.update(operations=d['operations']-1)))
        first=checker.ROUTES[0][2]
        reject('omit a complete old/new row',lambda:edit('CUTS.json',lambda d:d[first]['complete_parent_to_new_rows'].pop()))
        reject('claim a false sole consumer',lambda:edit('CUTS.json',lambda d:d[first].update(q4_consumers=[])))
        reject('forget one whole direct route',lambda:edit('CUTS.json',lambda d:d.pop(first)))
        reject('wrong global degree',lambda:edit(first+'.json',lambda d:d.update(exact_degree=1)))
        reject('changed positive domain',lambda:edit(first+'.json',lambda d:d.update(domain='all integers')))
        reject('changed whole copied old graph',lambda:edit('parents/ten-positive-saturated-pell/direct_saturated_upper.json',lambda d:row(d,'P1').__setitem__(3,1)))
        reject('changed inherited whole degree record',lambda:edit('parents/ten-positive-saturated-pell/CHECK.json',lambda d:d.update(status='FAIL')))
        reject('changed inherited ordinary proof',lambda:(folder/'parents/ten-positive-uncentered-b-weight/PROOF.md').write_text('assume transport positive\n'))
        reject('old-onlyK splice into indexed binding',lambda:edit('INDEXED_BINDING.json',lambda d:d['ports']['K0'].update(json.loads(payload[first+'.json'])['coefficient_binding']['ports']['K0'])))
        reject('oldK payload in indexed tuple',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').write_bytes(payload['coefficients/compact44_bfs/K.bin.gz']))
        reject('changed whole beta payload',lambda:(folder/'coefficients/compact44_bfs/beta.bin.gz').write_bytes(b'not a coefficient'))
        pin=next(iter(json.loads(payload['SOURCE_PINS.json'])['files']))
        reject('drop whole dependency pin',lambda:edit('SOURCE_PINS.json',lambda d:d['files'].pop(pin)))
        reject('drop calibrated parent seal',lambda:edit('SOURCE_PINS.json',lambda d:d['closed_dependencies'].pop(next(iter(d['closed_dependencies'])))))
        reject('omit nested manifest from closure',lambda:edit('MANIFEST.json',lambda d:d['files'].pop('nested/MANIFEST.json')),True)
        reject('unlisted closed artifact',lambda:(folder/'unlisted.txt').write_text('unlisted\n'),True)
        reject('changed sealed new proof',lambda:(folder/'PROOF.md').write_text('circuit count hides one gate\n'),True)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),reviewed_core=PINS,positive_controls=['complete unsealed packet','complete sealed packet including nested manifest','same receipt idempotent','different receipt preserved'],rejected_actual_artifacts=rejected,rejected_count=len(rejected),exact_author_checker_imported=True,producer_or_parent_or_incoming_code_executed=False,frozen_inputs_modified=False,audit_sha256=digest(Path(__file__).read_bytes()))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),rejected_actual_artifacts=len(rejected),positive_controls=4),sort_keys=True))
if __name__=='__main__':main()
