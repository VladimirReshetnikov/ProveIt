#!/usr/bin/env python3
"""Retain exact raw arithmetic wires to obtain small-height integer quartics."""
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
DEST=ROOT/'candidates/retained-radius-integers'
PARENT=ROOT/'candidates/projected-factorial-radius'
ARCHIVE=REPO/'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
BASE='ConZFC_407_888_Quartics/code/integer_pipeline/'
CONFIGS=[('integer1742',0,None),('integer1095',2,1),('integer950',2,2),('integer886',4,2),('integer872',8,2)]


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def encoded(obj):return(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()


def expand(eq):
    out={}
    for row in eq['residuals']:
        for c,m in row['terms']:
            for d,n in row['terms']:
                key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    out={m:c for m,c in out.items()if c}
    metrics=dict(variables=len(eq['variables']),quadratic_rows=len(eq['residuals']),exact_degree=max(map(len,out)),
                 expanded_monomials=len(out),max_abs_expanded_coefficient=max(map(abs,out.values())),
                 max_abs_row_coefficient=max(abs(c)for r in eq['residuals']for c,m in r['terms']))
    return dict(schema='sparse_integer_polynomial_v1',domain=eq['domain'],variables=len(eq['variables']),
                terms=[[c,list(m)]for m,c in sorted(out.items())]),metrics


def build():
    need(digest(ARCHIVE.read_bytes())==PIN,'whole reviewed engine archive')
    raw=json.loads((PARENT/'both_source/raw_builder.json').read_text())
    parent=dict(schema='finite_quadratic_residuals_v1',domain='nonnegative integers',
                polynomial='sum(square(row) for row in residuals)',variables=raw['variables'],
                residuals=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']])
    polynomial,metrics=expand(parent);parent['metrics']=metrics
    need(metrics['variables']==1259 and metrics['quadratic_rows']==1177 and metrics['max_abs_expanded_coefficient']==427,'complete raw source metrics')
    files={'raw_natural.json':encoded(parent),'raw_polynomial.json':encoded(polynomial)};members={};census={}
    with tempfile.TemporaryDirectory(prefix='retained-radius-engine-')as tmp,zipfile.ZipFile(ARCHIVE)as z:
        temp=Path(tmp);code=temp/'code';code.mkdir()
        for member in z.namelist():
            if member.startswith(BASE)and member.endswith('.py'):
                data=z.read(member);(code/Path(member).name).write_bytes(data);members[member]=digest(data)
        sys.path.insert(0,str(code))
        import build_integer
        import terminal_elimination as elimination
        source=temp/'raw_natural.json';source.write_bytes(files['raw_natural.json'])
        with redirect_stdout(io.StringIO()):build_integer.main(source,temp/'full',0)
        signed=json.loads((temp/'full/guarded.json').read_text());conversion=json.loads((temp/'full/domain_conversion.json').read_text())
        files['guarded.json']=encoded(signed);files['domain_conversion.json']=encoded(conversion)
        for name,cap,affine in CONFIGS:
            child,cert,met=elimination.optimize(signed,max_support=cap,affine_support=affine)
            check=elimination.verify(signed,child,cert)
            need(cert['unconstrained_removed']==[],'complete integer restoration with no free removals')
            poly=elimination.expand(child);census[name]=met
            packet={'equation.json':child,'expanded_polynomial.json':poly,'elimination_certificate.json':cert,
                    'BUILD.json':dict(status='PASS',metrics=met,projection=check)}
            for file,obj in packet.items():files[name+'/'+file]=encoded(obj)
    pins=dict(parent='candidates/projected-factorial-radius',parent_files={name:digest((PARENT/name).read_bytes())for name in
              ['both_source/raw_builder.json','both_source/gate_ledger.json','both_source/equation.json','PROOF.md']},
              engine_archive=str(ARCHIVE.relative_to(REPO)),engine_archive_sha256=PIN,arithmetic_source_members=members,
              independent_raw_export_tool='tools/review_quartics407888.py',
              independent_raw_export_tool_sha256=digest((ROOT/'tools/review_quartics407888.py').read_bytes()),
              independent_restoration_controls='candidates/projected-radius-integers/check.py',
              independent_restoration_controls_sha256=digest((ROOT/'candidates/projected-radius-integers/check.py').read_bytes()),
              scope='Actual raw gate rows retained; every sign guard and integer projection is recomputed. Frozen parents unchanged.')
    files['PARENT_PINS.json']=encoded(pins);files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
         sha256={name:digest(data)for name,data in files.items()},scope='Exact raw-source/sign/projection family; independent checker and ordinary proof separate. No Lean.'))
    return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=build()
    for name,raw in files.items():
        path=DEST/name
        if args.check:need(path.read_bytes()==raw,'byte-exact retained-wire sibling '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,metrics=census),indent=2))


if __name__=='__main__':main()
