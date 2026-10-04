#!/usr/bin/env python3
"""Deterministic interleaving probes of inspected release-tool boundaries.
Only scratch release copies and external probe files are changed. No science code runs.
"""
import hashlib,json,runpy,shutil,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
RESULTS=[]
for case in ('manifest-output-race','archive-output-race','archive-input-race'):
    root=HERE/'scratch'/('probe-'+case);shutil.copytree(HERE/'scratch/pristine',root)
    out=HERE/'outputs'/('probe-'+case)
    before={p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}
    m=runpy.run_path(str(root/'tools/release59.py'),run_name='inspected_release_probe')
    original=m['fresh_file'];g=m['main'].__globals__
    def hook(raw):
        result=original(raw)
        if case=='archive-input-race':
            p=root/'qa/PRESENTATION_RECEIPT.json';p.write_bytes(p.read_bytes()+b'\nRACED-IN CHANGE\n')
        else:result.write_bytes(b'EXTERNAL CONCURRENT WRITER\n')
        return result
    g['fresh_file']=hook
    pin=hashlib.sha256((root/'MANIFEST.json').read_bytes()).hexdigest()
    sys.argv=['release59.py',*(['manifest','--output',str(out)] if case.startswith('manifest') else ['archive','--manifest-sha256',pin,'--output',str(out)])]
    try:
        m['main']();error=None;accepted=True
    except Exception as e:error=str(e);accepted=False
    result={'case':case,'accepted':accepted,'error':error,'output_exists':out.exists(),'concurrent_output_preserved':out.exists() and out.read_bytes()==b'EXTERNAL CONCURRENT WRITER\n'}
    if case=='archive-input-race' and out.exists():
        import zipfile
        with zipfile.ZipFile(out) as z:
            manifest=json.loads(z.read('MANIFEST.json'))
            result['archive_matches_embedded_manifest']=all(hashlib.sha256(z.read(n)).hexdigest()==r['sha256'] for n,r in manifest['files'].items())
    RESULTS.append(result)
    shutil.rmtree(root)
(HERE/'RELEASE_RACE_PROBES.json').write_text(json.dumps(RESULTS,sort_keys=True,indent=2)+'\n')
print(json.dumps(RESULTS,sort_keys=True,indent=2))
