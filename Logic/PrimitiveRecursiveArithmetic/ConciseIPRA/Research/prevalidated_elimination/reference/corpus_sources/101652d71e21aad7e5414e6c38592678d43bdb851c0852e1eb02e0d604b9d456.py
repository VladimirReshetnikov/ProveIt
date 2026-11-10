"""Recheck the pinned ZIP census without executing any archived Python code.

Usage: python3 audit_corpus.py /path/to/ProveIt/docs/drafts
The directory must contain the exact 16 pinned archive byte strings.
"""
import hashlib
import io
import json
from pathlib import Path
import sys
import zipfile
from measure import metrics

ROOT=Path(__file__).resolve().parent

def scan(raw,location,depth=0):
    if depth>10:
        raise ValueError('Unexpected archive nesting')
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for info in archive.infolist():
            if info.filename.endswith('.py'):
                data=archive.read(info)
                try:
                    yield dict(location=location+'!'+info.filename,depth=depth,**metrics(data))
                except (SyntaxError,UnicodeDecodeError) as error:
                    yield dict(location=location+'!'+info.filename,depth=depth,error=str(error))
            elif info.filename.endswith('.zip'):
                yield from scan(archive.read(info),location+'!'+info.filename,depth+1)

def main():
    if len(sys.argv)!=2:
        raise SystemExit(__doc__)
    directory=Path(sys.argv[1])
    snapshot=json.loads((ROOT/'evidence/repository_snapshot.json').read_text())
    rows=[]
    for entry in sorted(snapshot['drafts'],key=lambda x:x['name']):
        raw=(directory/entry['name']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if blob!=entry['sha'] or len(raw)!=entry['size'] or hashlib.sha256(raw).hexdigest()!=entry['sha256']:
            raise ValueError('Wrong pinned archive '+entry['name'])
        rows.extend(scan(raw,entry['name']))
    expected=json.loads((ROOT/'evidence/all_python_metrics.json').read_text())['records']
    if rows!=expected:
        raise ValueError('Census mismatch; use recorded CPython3.12.14 and exact archives')
    classification=json.loads((ROOT/'evidence/corpus_classification.json').read_text())
    print(json.dumps({'archives':len(snapshot['drafts']),
                      'counts':classification['counts'],
                      'claimed_envelope':classification['claimed_envelope'],
                      'census_identical':True},indent=2))

if __name__=='__main__':
    main()
