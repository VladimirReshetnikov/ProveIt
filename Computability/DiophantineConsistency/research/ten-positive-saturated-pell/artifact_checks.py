#!/usr/bin/env python3
"""Feed complete malformed private artifacts to the exact reviewed SAT checker."""
import argparse
from contextlib import redirect_stdout
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util,io,json,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PINS = {'README.md': '29835a17b6b420847c097052d57f92675201ad172a1eaf3780a777de25b66437', 'PROOF.md': '3c8fd4dc56ba4a39541301efc26ff25aeb50a0c5f8329f0c41f95c17dbf8f512', 'SOURCE_PINS.json': '1cd090f108fffa44276d3382f90c5d54b3031d4e6d417847ca53add9e88e9fb3', 'INCOMING_MEMBERS.json': 'e7717b1d4830d9cb20444344e9e660b36309bc9ab9864e894abb1a92cc58b61f', 'build.py': '32d0e9b948c5e8cc55788e30b6808909dc974dd964fc2b25ee8fd06efee780c0', 'check.py': 'e6976b0f157209533324f6200068612d8b91c12d498ecb69d260ccb1281f3e0d'}
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(blob):return sha256(blob).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    for name,pin in PINS.items():need(digest((HERE/name).read_bytes())==pin,'whole reviewed author core '+name)
    payload={str(p.relative_to(HERE)):p.read_bytes() for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'};payload['nested/MANIFEST.json']=b'{}\n'
    spec=importlib.util.spec_from_file_location('reviewed_saturated_checker',HERE/'check.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    rejected=[]
    with tempfile.TemporaryDirectory(prefix='saturated-pell-artifacts-') as directory:
        base=Path(directory);folder=base/'packet';output=base/'receipt.json';checker.HERE=folder;checker.ROOT=ROOT
        def reset(sealed=False):
            if folder.exists():
                for p in sorted(folder.rglob('*'),key=lambda p:len(p.parts),reverse=True):p.unlink() if p.is_file() else p.rmdir()
            folder.mkdir(exist_ok=True)
            for name,blob in payload.items():
                target=folder/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(blob)
            if sealed:(folder/'MANIFEST.json').write_text(json.dumps(dict(files={n:digest(b) for n,b in payload.items()}),sort_keys=True)+'\n')
            if output.exists():output.unlink()
        def replay():
            previous=sys.argv;sys.argv=['reviewed-check.py','--output',str(output)]
            try:
                with redirect_stdout(io.StringIO()):checker.main()
            finally:sys.argv=previous
        def edit(name,action):
            p=folder/name;data=json.loads(p.read_bytes());action(data);p.write_text(json.dumps(data,sort_keys=True)+'\n')
        def row(d,name):return next(r for r in d['source'] if r[0]==name)
        def reject(name,mutation,sealed=False):
            reset(sealed);mutation()
            try:replay()
            except (ValueError,KeyError,TypeError,IndexError,OSError,EOFError) as error:rejected.append(dict(name=name,exception=type(error).__name__,reason=str(error)))
            else:raise ValueError('actual checker accepted malformed artifact '+name)
        reset();replay();need(json.loads(output.read_bytes())['status']=='PASS','whole unsealed positive control')
        reset(True);replay();need(json.loads(output.read_bytes())['status']=='PASS','whole closed positive control with nested manifest')
        for stem in ['saturated_upper','saturated_sharp','direct_saturated_upper','direct_saturated_sharp']:
            name=stem+'.json'
            reject(stem+':wrong final norm sign',lambda n=name:edit(n,lambda d:row(d,'N').__setitem__(1,'+')))
            reject(stem+':omit coprime E factor',lambda n=name:edit(n,lambda d:row(d,'Dg').__setitem__(2,1)))
            reject(stem+':change quantified domain',lambda n=name:edit(n,lambda d:d.update(domain='unrestricted integers')))
        reject('wrong upper center',lambda:edit('saturated_upper.json',lambda d:row(d,'Cg').__setitem__(2,'Am1')))
        reject('direct drops extra q from carrier',lambda:edit('direct_saturated_upper.json',lambda d:row(d,'P1').__setitem__(2,'q3')))
        def load_old_K():return json.loads(payload['saturated_upper.json'])['coefficient_binding']['ports']['K0']
        reject('indexed binding points at oldK only',lambda:edit('INDEXED_BINDING.json',lambda d:d['ports']['K0'].update(load_old_K())))
        def bad_MF():
            a=int.from_bytes(gzip.decompress(payload['coefficients/compact44_bfs/MF_source.bin.gz']),'little');b=int.from_bytes(gzip.decompress(payload['coefficients/compact44_bfs/beta.bin.gz']),'little');v=a+b
            (folder/'coefficients/compact44_bfs/MF_source.bin.gz').write_bytes(gzip.compress(v.to_bytes((v.bit_length()+7)//8,'little'),mtime=0))
        reject('MF shifted twice',bad_MF)
        reject('replace indexed whole K by old BFS bytes',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').write_bytes(payload['coefficients/compact44_bfs/K.bin.gz']))
        reject('append noncanonical whole-coefficient zero byte',lambda:(folder/'coefficients/compact44_bfs/K.bin.gz').write_bytes(gzip.compress(gzip.decompress(payload['coefficients/compact44_bfs/K.bin.gz'])+b'\x00',mtime=0)))
        reject('copied unbounded proof changed',lambda:(folder/'source/saturation_semantics.tex').write_text('we assume tau is integral\n'))
        reject('copied global degree proof changed',lambda:(folder/'source/saturated_degree_proof.tex').write_text('degree is inferred only from a ray\n'))
        reject('reviewed incoming verifier record changed',lambda:edit('REVIEWED_INCOMING_VERIFICATION.json',lambda d:d.update(status='FAIL')))
        first=next(iter(json.loads(payload['INCOMING_MEMBERS.json'])))
        reject('whole archive member pin changed',lambda:edit('INCOMING_MEMBERS.json',lambda d:d[first].update(sha256='0'*64)))
        firstdep=next(iter(json.loads(payload['SOURCE_PINS.json'])['files']))
        reject('whole inherited dependency pin changed',lambda:edit('SOURCE_PINS.json',lambda d:d['files'].update({firstdep:'0'*64})))
        reject('closed inventory omits nested manifest',lambda:edit('MANIFEST.json',lambda d:d['files'].pop('nested/MANIFEST.json')),True)
        reject('closed inventory rejects unlisted member',lambda:(folder/'unlisted.json').write_text('{}\n'),True)
        reject('closed inventory authenticates author proof',lambda:(folder/'PROOF.md').write_text('wrong proof\n'),True)
        reject('closed inventory rejects missing numeral',lambda:(folder/'coefficients/indexed_bfs/K.bin.gz').unlink(),True)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),reviewed_files=PINS,positive_controls=['whole unsealed packet','whole closed packet including nested manifest fixture'],rejected_actual_artifacts=rejected,rejected_count=len(rejected),checker_imported=True,builder_or_incoming_or_parent_code_executed=False,immutable_inputs_modified=False,unbounded_proof_replaced_by_controls=False,audit_sha256=digest(Path(__file__).read_bytes()))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',rejected_actual_artifacts=len(rejected),positive_controls=2),sort_keys=True))
if __name__=='__main__':main()
