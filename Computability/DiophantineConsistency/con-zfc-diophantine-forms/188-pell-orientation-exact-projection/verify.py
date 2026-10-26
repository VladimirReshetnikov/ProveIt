#!/usr/bin/env python3
"""Offline verification for the complete release. Standard library only."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, subprocess, sys, tempfile, zipfile

ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok: raise ValueError(msg)

def run(relative,args=()):
    p=ROOT/relative
    r=subprocess.run([sys.executable,'-B',str(p),*args],cwd=p.parent,
                     text=True,capture_output=True,check=True)
    return json.loads(r.stdout)

def verify_source():
    rec=json.loads((ROOT/'provenance/ROOT_SOURCE_AUTHENTICATION.json').read_text())
    p=ROOT/'direct/inherited/ConZFC_Cofinal_Pell_Compression_2026-10-25.zip'
    data=p.read_bytes()
    need(hashlib.sha256(data).hexdigest()==rec['archive_sha256'],'inherited archive hash')
    git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    need(git==rec['git_blob_sha1'],'immutable Git archive identity')
    with zipfile.ZipFile(p) as z:
        b=z.read(rec['member'])
    need(b==(ROOT/'direct/parent206.json').read_bytes(),'literal parent archive member')
    need(hashlib.sha256(b).hexdigest()==rec['parent206_sha256'],'parent source hash')
    source136={
      'signed_section.tex':'9efee27f8b1b2927675c89a20829ec6a5a626f8a',
      'report.tex':'d090040d1b4607103027d35d69c8a1ae5698d7df',
      'LICENSE':'9ba84db3ce7197b149cadca52befe271bda64d8b',
      'NOTICE.txt':'fb4d5a128170f6b06111727d9a80ca2ef76299c9'}
    for name,expected in source136.items():
        b=(ROOT/'provenance'/('source136_'+name)).read_bytes()
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==expected,
             'source136 immutable blob '+name)
    b=(ROOT/'provenance/source177_README.md').read_bytes()
    need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==
         'b113ca65c03b81293e1a8e55073376c0c95e2972','source177 comparison source')
    return {'archive_git_blob':git,'parent206_sha256':rec['parent206_sha256'],
            'source136_files':len(source136)}

def verify_report_tables():
    # Regenerate into a private temporary directory and require byte identity.
    # The report generator reads only the already audited literal source data.
    spec=importlib.util.spec_from_file_location('release_report_generator',ROOT/'build_report.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    import contextlib,io
    with tempfile.TemporaryDirectory(prefix='conzfc_report_') as t:
        module.GEN=Path(t)
        with contextlib.redirect_stdout(io.StringIO()): module.main()
        names=[]
        for p in sorted(Path(t).glob('*.tex')):
            need(p.read_bytes()==(ROOT/'generated'/p.name).read_bytes(),'generated report table '+p.name)
            names.append(p.name)
    return names

def verify_manifest():
    p=ROOT/'MANIFEST.json'
    if not p.exists():return {'status':'not yet sealed'}
    d=json.loads(p.read_text())
    for r in d['files']:
        b=(ROOT/r['path']).read_bytes()
        need(len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],
             'release member '+r['path'])
    return {'status':'PASS','members':len(d['files'])}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    source=verify_source()
    direct=run('direct/independent_review.py',['--corruption-controls'])
    printed=run('direct/check_printed.py')
    native=run('native/verify.py')
    tables=verify_report_tables()
    manifest=verify_manifest()
    receipt={'status':'PASS','source_authentication':source,
             'direct':direct,'printed_definition':printed,'native':native,
             'report_tables':tables,'manifest':manifest,
             'scope':'Finite artifact authentication and algebra; the ordinary unbounded calibration is retained separately.'}
    s=json.dumps(receipt,indent=2,sort_keys=True)+'\n'
    if a.receipt:a.receipt.write_text(s)
    print(s)

if __name__=='__main__':main()
