#!/usr/bin/env python3
"""Replay a sealed round-7 artifact, without Lean, network, or upstream writes."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, zipfile

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive',type=Path)
    parser.add_argument('--output-dir',type=Path)
    args=parser.parse_args()
    zpath=args.archive.resolve()
    require(zpath.is_file(),'Archive not found')
    output=args.output_dir.resolve() if args.output_dir else None
    if output: output.mkdir(parents=True,exist_ok=True)
    commands=[]
    with tempfile.TemporaryDirectory(prefix='proveit-round7-sealed-') as tmp:
        t=Path(tmp); extracted=t/'extracted'; extracted.mkdir()
        with zipfile.ZipFile(zpath) as z:
            require(z.testzip() is None,'ZIP CRC failed')
            names=z.namelist()
            require(len(set(names))==len(names),'Duplicate ZIP member')
            require(sum(i.file_size for i in z.infolist())<100_000_000,'Unexpected inflated size')
            for i in z.infolist():
                p=Path(i.filename)
                require(not p.is_absolute() and '..' not in p.parts,'Unsafe ZIP path')
                require((i.external_attr >> 16) & 0o170000 != 0o120000,'ZIP symlink refused')
            z.extractall(extracted)
        root=extracted/'LeanReview7'
        require(root.is_dir(),'Unexpected archive root')
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
        def run(cmd,cwd=root,expected=0):
            p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True)
            record={'command':cmd,'exit':p.returncode,'expected':expected}
            commands.append(record)
            if output: (output/f'command_{len(commands):02d}.txt').write_text(p.stdout+p.stderr)
            require(p.returncode==expected,'Replay command failed: '+str(cmd)+'\n'+p.stdout+p.stderr)
            return p
        run([sys.executable,'verify_bundle.py','--strict'])
        for script in ['provenance/verify_snapshot.py','baseline_audit/verify_audit.py',
                       'research/outer_seed/check_candidate.py',
                       'independent_review/check_lemma_reuse.py']:
            run([sys.executable,script]); run([sys.executable,'-O',script])
        run([sys.executable,'independent_review/selftest_lemma_reuse.py'])
        run([sys.executable,'-O','independent_review/selftest_lemma_reuse.py'])
        # Three independent mutations of a disposable copy, never the sealed tree.
        negative=t/'negative'; shutil.copytree(root,negative)
        p=negative/'README.md'; old=p.read_bytes()
        p.write_bytes(old+b'\ncorruption\n'); run([sys.executable,'-O','verify_bundle.py','--strict'],negative,1)
        p.write_bytes(old); p.unlink(); run([sys.executable,'-O','verify_bundle.py','--strict'],negative,1)
        p.write_bytes(old); (negative/'UNEXPECTED').write_text('extra')
        run([sys.executable,'-O','verify_bundle.py','--strict'],negative,1)
        rebuilt=t/'report_rebuild'; shutil.copytree(root/'report',rebuilt)
        run(['bash','build.sh'],rebuilt)
        import fitz
        first=fitz.open(root/'report/proof_simplification_report.pdf')
        second=fitz.open(rebuilt/'proof_simplification_report.pdf')
        require(len(first)==len(second),'PDF page count differs')
        pages=[]
        for index,(a,b) in enumerate(zip(first,second),1):
            te=a.get_text()==b.get_text()
            pe=a.get_pixmap(matrix=fitz.Matrix(1,1)).samples==b.get_pixmap(matrix=fitz.Matrix(1,1)).samples
            require(te and pe,'PDF text/pixel mismatch page '+str(index))
            pages.append({'page':index,'text_equal':te,'pixels_equal_72dpi':pe})
        run([sys.executable,'verify_bundle.py','--strict'])
        result={'status':'PASS_SEALED_NON_LEAN_REPLAY','archive_bytes':zpath.stat().st_size,
                'archive_sha256':hashlib.sha256(zpath.read_bytes()).hexdigest(),
                'commands':commands,'PDF_pages':pages,'new_local_edits':1,
                'local_lines_saved':10,'Lean_elaboration':'NOT_RUN',
                'scope':'Source/exclusion evidence, exact edit, finite arithmetic, integrity, and PDF replay only',
                'incoming_archive_bytes':'Not included; exact intake receipts and extracted-evidence identities only'}
        if output: (output/'SEALED_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
if __name__=='__main__':
    try: main()
    except Exception as e:
        print('FAIL: '+str(e),file=sys.stderr); raise SystemExit(1)
