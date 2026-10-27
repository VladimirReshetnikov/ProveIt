"""Extract a supplied release ZIP and replay four check suites plus integrity."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,zipfile

def main(archive,output):
    archive=Path(archive).resolve()
    records=[]
    with tempfile.TemporaryDirectory(prefix='eth-replay-') as tmp:
        tmp=Path(tmp)
        with zipfile.ZipFile(archive) as z:
            for name in z.namelist():
                target=(tmp/name).resolve()
                if not target.is_relative_to(tmp):raise ValueError('unsafe archive path')
            if z.testzip() is not None:raise ValueError('CRC failure')
            z.extractall(tmp)
        root=tmp/'eth_matching_refinement'
        def run(args,expect=0):
            p=subprocess.run([sys.executable,'-B']+args,cwd=root,text=True,capture_output=True)
            records.append(dict(args=args,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
            if (p.returncode==0)!=(expect==0):raise RuntimeError(records[-1])
        run(['code/verify_bundle.py'])
        for opt in ([],['-O']):
            suffix='optimized' if opt else 'normal'
            run(opt+['code/verify.py',str(tmp/f'replay-{suffix}.json')])
            run(opt+['qa/independent_code_checks.py',str(tmp/f'independent-{suffix}.json')])
        run(['code/verify_bundle.py'])
        # Negative controls are performed only in the temporary extracted copy.
        readme=root/'README.txt'; original=readme.read_bytes()
        readme.write_bytes(original+b'\nchanged\n')
        run(['code/verify_bundle.py'],expect=1)
        readme.write_bytes(original)
        readme.rename(root/'README.missing')
        run(['code/verify_bundle.py'],expect=1)
        (root/'README.missing').rename(readme)
        sums=root/'SHA256SUMS'; saved=sums.read_text()
        src=root/'sources/08_build_quantitative-contraction.tex'; oldsrc=src.read_bytes()
        src.write_bytes(oldsrc+b'\n')
        altered=[]
        for line in saved.splitlines():
            digest,name=line.split('  ',1)
            if name==str(src.relative_to(root)):digest=hashlib.sha256(src.read_bytes()).hexdigest()
            altered.append(digest+'  '+name)
        sums.write_text('\n'.join(altered)+'\n')
        run(['code/verify_bundle.py'],expect=1)
        src.write_bytes(oldsrc);sums.write_text(saved)
        run(['code/verify_bundle.py'])
    result=dict(success=True,archive=archive.name,sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                records=records,positive_stages=7,negative_integrity_controls=3,
                scope='Extracted-ZIP finite component replay and sealed-file checks; not full SAT validation.')
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))

if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit('usage: replay_archive.py ARCHIVE.zip OUTPUT.json')
    main(sys.argv[1],sys.argv[2])
