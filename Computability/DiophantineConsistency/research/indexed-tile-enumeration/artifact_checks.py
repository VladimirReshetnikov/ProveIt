#!/usr/bin/env python3
"""Run the exact reviewed checker on fresh complete private artifact mutations."""
import argparse
from contextlib import redirect_stdout
import gzip
from hashlib import sha256
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PINS = {'README.md': '38732b2a57e28cf8d23d8bfd0508840d14435ce1204878b90524ba2cf2dd4f25', 'PROOF.md': 'b9810eb5aaa7cbfeb7f076a31b6daad6e3e39d05ad7592adb7abf6f0e9515177', 'SOURCE_PINS.json': 'd9a74b9c9c3dd3af76b7afd9125fe76bed35e0509c0dd7930a5a23b71d0bb2ac', 'build.py': '131041bfccac8ad9284da223a372d87d513c3e31b7da4154075336bf6910670b', 'check.py': 'a0338d358a04eae59e0121799502dcf58969fb73898ead5e1e77644702418ccf', 'render.py': '44dbd689ee2fdc2b1655806acbca123197259283c6b2e5068826725bbb5f1d15'}
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(blob):return sha256(blob).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    for name,pin in PINS.items():need(digest((HERE/name).read_bytes())==pin,'reviewed complete member '+name)
    names=list(PINS)+['SEED.txt','TILES.json','NATIVE_CERTIFICATE.json','polynomial.json','equation.tex','equation.pdf','equation.txt']
    names+=['coefficients/'+n for n in ['BINDING.json','beta.bin.gz','K.bin.gz','MC.bin.gz','MF_source.bin.gz']]
    payload={n:(HERE/n).read_bytes() for n in names};payload['nested/MANIFEST.json']=b'{}\n'
    spec=importlib.util.spec_from_file_location('reviewed_indexed_tiles_checker',HERE/'check.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    rejected=[]
    with tempfile.TemporaryDirectory(prefix='indexed-tiles-artifacts-') as directory:
        base=Path(directory);folder=base/'packet';output=base/'receipt.json';checker.HERE=folder;checker.ROOT=ROOT
        def reset(sealed=False):
            if folder.exists():
                for p in sorted(folder.rglob('*'),key=lambda p:len(p.parts),reverse=True):p.unlink() if p.is_file() else p.rmdir()
            folder.mkdir(exist_ok=True)
            for name,data in payload.items():
                target=folder/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
            if sealed:(folder/'MANIFEST.json').write_text(json.dumps({'files':{n:digest(b) for n,b in payload.items()}},sort_keys=True)+'\n')
            if output.exists():output.unlink()
        def replay():
            previous=sys.argv;sys.argv=['reviewed-check.py','--output',str(output)]
            try:
                with redirect_stdout(io.StringIO()):checker.main()
            finally:sys.argv=previous
        def edit(name,action):
            p=folder/name;data=json.loads(p.read_bytes());action(data);p.write_text(json.dumps(data,sort_keys=True)+'\n')
        def replace(name,old,new):
            p=folder/name;text=p.read_text();need(old in text,'mutation target present');p.write_text(text.replace(old,new,1))
        def reject(name,mutation,sealed=False):
            reset(sealed);mutation()
            try:replay()
            except (ValueError,KeyError,TypeError,IndexError,OSError,EOFError) as error:rejected.append(dict(name=name,exception=type(error).__name__,reason=str(error)))
            else:raise ValueError('actual checker accepted mutated artifact: '+name)
        reset();replay();need(json.loads(output.read_bytes())['status']=='PASS','complete unsealed positive control')
        reset(True);replay();need(json.loads(output.read_bytes())['status']=='PASS','complete closed positive control with nested manifest fixture')
        for index,label in [(0,'Start'),(1,'Forbidden'),(2,'transition'),(436,'right move'),(834,'left move'),(924,'cleanup'),(929,'literal initializer'),(942,'bottom')]:
            reject('wrong '+label+' tuple',lambda i=index:edit('TILES.json',lambda d:d[i].__setitem__(3,d[i][3]+1)))
        reject('truncated seed',lambda:replace('SEED.txt',payload['SEED.txt'].decode(),payload['SEED.txt'].decode()[:-3]+'\n'))
        reject('changed seed symbol',lambda:replace('SEED.txt',payload['SEED.txt'].decode()[0],'0' if payload['SEED.txt'][:1]!=b'0' else '1'))
        reject('coherent binding wrong bit length',lambda:edit('coefficients/BINDING.json',lambda d:d['ports']['K0'].update(bits=1)))
        reject('reuse old sorted BFS K',lambda:(folder/'coefficients/K.bin.gz').write_bytes((checker.BASE/'coefficients/K.bin.gz').read_bytes()))
        reject('noncanonical trailing byte in K',lambda:(folder/'coefficients/K.bin.gz').write_bytes(gzip.compress(gzip.decompress(payload['coefficients/K.bin.gz'])+b'\x00',mtime=0)))
        reject('changed MC whole numeral',lambda:(folder/'coefficients/MC.bin.gz').write_bytes(gzip.compress(bytes([0])+gzip.decompress(payload['coefficients/MC.bin.gz'])[1:],mtime=0)))
        def double_shift():
            n=int.from_bytes(gzip.decompress(payload['coefficients/MF_source.bin.gz']),'little')+int.from_bytes(gzip.decompress(payload['coefficients/beta.bin.gz']),'little')
            (folder/'coefficients/MF_source.bin.gz').write_bytes(gzip.compress(n.to_bytes((n.bit_length()+7)//8,'little'),mtime=0))
        reject('MF source shifted twice',double_shift)
        reject('old controller H0 residue',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d['audit']['controller'][0].update(H0=46)))
        reject('selector permutation does not fix Start',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d['selector_old_to_new'].__setitem__(0,1)))
        reject('wrong state permutation',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d['state_old_to_BFS'].__setitem__(93,93)))
        reject('old unrenamed initializer in certificate',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d.update(literal_initializer=[3,436,4,188])))
        reject('claim pointwise native-word reuse',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d.update(old_native_words_reused=True)))
        reject('wrong carry threshold',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d['audit'].update(carry_threshold=1)))
        reject('wrong multiplicative order',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d['audit']['orders'][2].update(order=581195)))
        reject('omit finite support metadata',lambda:edit('NATIVE_CERTIFICATE.json',lambda d:d['audit'].pop('support_count')))
        reject('changed arithmetic gate',lambda:edit('polynomial.json',lambda d:d['source'][0].__setitem__(3,2)))
        reject('changed positive domain',lambda:edit('polynomial.json',lambda d:d.update(domain='unrestricted integers')))
        reject('wrong operation count',lambda:edit('polynomial.json',lambda d:d.update(operations=97)))
        reject('wrong exact degree',lambda:edit('polynomial.json',lambda d:d.update(exact_degree=368)))
        reject('wrong output port',lambda:edit('polynomial.json',lambda d:d.update(output='K0')))
        reject('printed transition wrong body',lambda:replace('equation.tex','d_jr_{u_j},v_j','d_jr_{u_j},v_j+1'))
        reject('printed right-target rank wrong definition',lambda:replace('equation.tex','r_q=6+','r_q=7+'))
        reject('printed initializer retained93',lambda:replace('equation.tex','929&(3,436,4,4)','929&(3,436,4,188)'))
        reject('printed Phi omits last selector',lambda:replace('equation.tex',r'\sum_{i=0}^{942}',r'\sum_{i=0}^{941}'))
        reject('printed decoder changed',lambda:replace('equation.tex',r'D_{216}',r'D_{215}'))
        reject('printed decoder seed truncated',lambda:replace('equation.tex',payload['SEED.txt'].decode().strip()[-2:]+r'\par',payload['SEED.txt'].decode().strip()[-2:-1]+r'\par'))
        reject('actual PDF replaced by old sorted page',lambda:(folder/'equation.pdf').write_bytes((checker.BASE/'equation.pdf').read_bytes()))
        reject('claimed PDF text differs from actual PDF',lambda:(folder/'equation.txt').write_text('wrong extracted text\n'))
        reject('closed inventory omits nested manifest',lambda:edit('MANIFEST.json',lambda d:d['files'].pop('nested/MANIFEST.json')),True)
        reject('closed inventory rejects extra member',lambda:(folder/'unlisted.json').write_text('{}\n'),True)
        reject('closed inventory authenticates README',lambda:(folder/'README.md').write_text('changed\n'),True)
        reject('closed inventory rejects missing numeral',lambda:(folder/'coefficients/K.bin.gz').unlink(),True)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),reviewed_files=PINS,positive_controls=['complete unsealed packet','complete closed inventory including nested MANIFEST fixture'],rejected_actual_artifacts=rejected,rejected_count=len(rejected),checker_imported=True,builder_or_renderer_or_optimizer_or_incoming_code_executed=False,immutable_inputs_modified=False,unbounded_proof_replaced_by_controls=False,audit_sha256=digest(Path(__file__).read_bytes()))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed artifact receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',rejected_actual_artifacts=len(rejected),positive_controls=2),sort_keys=True))
if __name__=='__main__':main()
