#!/usr/bin/env python3
"""New actual-row sign and signed monic certificates on the frozen 667 source."""
import argparse
from contextlib import redirect_stdout
from hashlib import sha256
import io
import json
from pathlib import Path
import sys
import tempfile
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
DEST=ROOT/'candidates/projected-radius-integers'
PARENT=ROOT/'candidates/projected-factorial-radius/both_source/equation.json'
ARCHIVE=REPO/'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
BASE='ConZFC_407_888_Quartics/code/integer_pipeline/'
CONFIGS=[('integer891',4),('integer865',8),('integer863',16),('integer862',32)]


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def encoded(obj):return(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()


def build():
    need(digest(ARCHIVE.read_bytes())==PIN,'whole accepted archive')
    raw=PARENT.read_bytes();parent=json.loads(raw)
    need(len(parent['variables'])==667 and len(parent['residuals'])==585,'exact frozen natural parent')
    files={};census={};members={}
    with tempfile.TemporaryDirectory(prefix='projected-radius-integer-engine-')as tmp,zipfile.ZipFile(ARCHIVE)as z:
        temp=Path(tmp);code=temp/'code';code.mkdir()
        for name in z.namelist():
            if name.startswith(BASE)and name.endswith('.py'):
                data=z.read(name);(code/Path(name).name).write_bytes(data);members[name]=digest(data)
        sys.path.insert(0,str(code))
        import build_integer
        shared=None
        for name,cap in CONFIGS:
            output=temp/name
            with redirect_stdout(io.StringIO()):build_integer.main(PARENT,output,cap)
            need((output/'source_natural.json').read_bytes()==raw,'unchanged exact natural source')
            packet={k:json.loads((output/k).read_text())for k in
                    ['guarded.json','domain_conversion.json','equation.json','expanded_polynomial.json','elimination_certificate.json','BUILD.json']}
            common={k:packet[k]for k in ['guarded.json','domain_conversion.json']}
            if shared is None:
                shared=common
                for k,value in common.items():files[k]=encoded(value)
            else:need(common==shared,'same exact sign proof/guarded parent for every projection')
            need(packet['elimination_certificate.json']['unconstrained_removed']==[],'no unconstrained coordinate removal')
            for k in ['equation.json','expanded_polynomial.json','elimination_certificate.json','BUILD.json']:files[name+'/'+k]=encoded(packet[k])
            census[name]=packet['BUILD.json']
        files['PARENT_PINS.json']=encoded(dict(parent_equation=str(PARENT.relative_to(ROOT)),parent_equation_sha256=digest(raw),
            parent_ordinary_proof='candidates/projected-factorial-radius/PROOF.md',
            parent_ordinary_proof_sha256=digest((PARENT.parent.parent/'PROOF.md').read_bytes()),
            archive=str(ARCHIVE.relative_to(REPO)),archive_sha256=PIN,arithmetic_source_members=members,
            scope='Actual new sign and monic certificates; old guard indices are not transferred by name.'))
        files['CENSUS.json']=encoded(census)
        files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
            sha256={name:digest(data)for name,data in files.items()},scope='Complete new integer companions; independent checker and ordinary proof are separate. No Lean.'))
        return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=build()
    for name,raw in files.items():
        path=DEST/name
        if args.check:need(path.read_bytes()==raw,'deterministic complete signed certificate '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,metrics={name:c['metrics']for name,c in census.items()}),indent=2))


if __name__=='__main__':main()
