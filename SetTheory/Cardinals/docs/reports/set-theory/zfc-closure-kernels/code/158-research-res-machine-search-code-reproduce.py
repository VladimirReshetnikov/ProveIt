#!/usr/bin/env python3
"""Build and replay the four pinned K218 bounded fold searches."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess

ROOT=Path(__file__).resolve().parent.parent
PIN='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
SEEDS={
    'primary':('k218.native.tm',PIN),
    'row157':('k218-row157.native.tm','3376bd149d5f35c03b3dabc79f095d2d2e674cf2e0e1c09a7de09431d8e74153'),
    'contextual':('k218-contextual.native.tm','3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1'),
    'contextual_row157':('k218-contextual_row157.native.tm','02ec4a475115217cd836f755e2806ba65a842a6377d13c7975a8ec81045819a5'),
}
FAMILIES={
    'equal':('full_two_row.cpp',23653),
    'shifted':('full_shifted_two_row.cpp',41167),
    'blank_equal':('blank_two_row.cpp',1917),
    'blank_shifted':('blank_shifted_two_row.cpp',3370),
    'observed_equal':('observed_two_row.cpp',23653),
    'observed_shifted':('observed_shifted_two_row.cpp',41167),
    'observed_equal_wide':('observed_two_row_wide.cpp',23653),
    'observed_shifted_wide':('observed_shifted_two_row_wide.cpp',41167),
}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--family',choices=['all',*FAMILIES],default='all')
    ap.add_argument('--seed',choices=list(SEEDS),default='primary')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--cxx',default='g++')
    a=ap.parse_args();filename,pin=SEEDS[a.seed];table=ROOT/'inputs'/filename
    if a.seed!='primary'and a.family!='equal':raise ValueError('Alternate seeds are packaged for the equal-head family only')
    if hashlib.sha256(table.read_bytes()).hexdigest()!=pin:raise ValueError('Pinned K218 bytes differ')
    a.output.mkdir(parents=True,exist_ok=False)
    names=list(FAMILIES)if a.family=='all'else[a.family]
    if any(name.startswith('observed_')for name in names):
        raw=gzip.decompress((ROOT/'inputs/finite-cases.txt.gz').read_bytes())
        manifest=json.loads((ROOT/'inputs/finite-case-manifest.json').read_text())
        if hashlib.sha256(raw).hexdigest()!=manifest['case_file_sha256']:raise ValueError('Finite-case pin mismatch')
        cases=a.output/'finite-cases.txt';cases.write_bytes(raw)
        for wide in sorted({name.endswith('_wide')for name in names if name.startswith('observed_')}):
            suffix='_wide'if wide else'';file_suffix='-wide'if wide else''
            collector=(a.output/('trace_contexts'+suffix)).resolve()
            subprocess.run([a.cxx,'-std=c++20','-O3',str(ROOT/'code'/('trace_contexts'+suffix+'.cpp')),'-o',str(collector)],check=True)
            with(a.output/('trace-contexts'+file_suffix+'-result.json')).open('w')as out:
                subprocess.run([str(collector),str(table),str(cases),str(a.output/('trace-contexts'+file_suffix+'.txt'))],check=True,stdout=out)
    for name in names:
        source,expected_pairs=FAMILIES[name];exe=(a.output/name).resolve()
        subprocess.run([a.cxx,'-std=c++20','-O3','-DNDEBUG',str(ROOT/'code'/source),'-o',str(exe)],check=True)
        with(a.output/(name+'-result.json')).open('w')as out,(a.output/(name+'.log')).open('w')as log:
            wide=name.endswith('_wide');radius='15'if wide else'7'
            command=[str(exe),str(table),str(a.output/(name+'-hit.tm')),str(a.seconds),radius]
            if name.startswith('observed_'):command.append(str(a.output/('trace-contexts-wide.txt'if wide else'trace-contexts.txt')))
            subprocess.run(command,check=True,stdout=out,stderr=log)
        receipt=json.loads((a.output/(name+'-result.json')).read_text())
        if receipt['status']=='COMPLETE':
            if receipt['pairs']!=expected_pairs or receipt['covered_rejections']!=expected_pairs*872**2:
                raise ValueError('Completed result has unexpected family count')
        print(name,json.dumps(receipt),flush=True)
        if receipt['status']=='HIT':
            print('A filter survivor needs independent diagram/runtime/startup verification.',flush=True)

if __name__=='__main__':main()
