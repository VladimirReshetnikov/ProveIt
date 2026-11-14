#!/usr/bin/env python3
"""Rebuild the complete recursive .tm inventory from the23 original ZIPs.

Usage: python3 scan_original_archives.py /path/to/ProveIt/docs/incoming output.json
Reads archives as data only; never executes archive code or extracts files.
Archive byte hashes deduplicate nested copied archives. Native start states
are not guessed: this scan only parses/counts literal transition tables.
"""
from pathlib import Path
import collections
import hashlib
import io
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parent


def parse(raw):
    rows = {}
    for lineno, line in enumerate(raw.decode('utf-8-sig').splitlines(),1):
        line = line.split('#')[0].strip()
        if not line:
            continue
        q,b,w,d,t = line.split()
        q,b,w,t = map(int,(q,b,w,t))
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:
            raise ValueError(f'bad or duplicated row{lineno}')
        rows[q,b] = w,d,t
    states = {q for q,b in rows}
    if not states or set(rows) != {(q,b)for q in states for b in(0,1)}:
        raise ValueError('empty or incomplete table')
    return rows


def digest(obj):
    return hashlib.sha256(json.dumps(obj,separators=(',',':')).encode()).hexdigest()


def main():
    if len(sys.argv)!=3:
        raise SystemExit(__doc__)
    incoming, output = map(Path,sys.argv[1:])
    expected = json.loads((ROOT/'archive_bytes_inventory.json').read_text())
    seen={};tables=[];bad=[]
    def visit(data,location,depth=0):
        h=hashlib.sha256(data).hexdigest()
        if h in seen:
            seen[h]['occurrences'].append(location)
            return
        z=zipfile.ZipFile(io.BytesIO(data))
        seen[h]={'sha256':h,'first_location':location,'occurrences':[location],
                 'bytes':len(data),'members':len(z.infolist()),'depth':depth}
        for m in z.infolist():
            if m.is_dir():continue
            if m.filename.lower().endswith('.zip'):
                visit(z.read(m),location+'!'+m.filename,depth+1)
            if m.filename.endswith('.tm'):
                b=z.read(m)
                try:r=parse(b)
                except Exception as exc:
                    bad.append({'location':location+'!'+m.filename,'reason':str(exc)})
                    continue
                tables.append({'archive_sha256':h,'archive':location,'member':m.filename,
                               'states':len({q for q,b in r}),'rows':len(r),
                               'sha256':hashlib.sha256(b).hexdigest(),
                               'parsed_sha256':digest([[q,b,*r[q,b]]for q,b in sorted(r)])})
    for item in sorted(expected,key=lambda x:Path(x['archive']).name):
        name=Path(item['archive']).name
        data=(incoming/name).read_bytes()
        if hashlib.sha256(data).hexdigest()!=item['sha256']:
            raise ValueError('pinned archive bytes differ: '+name)
        visit(data,name)
    result={'top_level_archives':len(expected),'unique_archives_recursive':len(seen),
            'maximum_nested_depth':max(x['depth']for x in seen.values()),
            'tables_in_unique_archives':len(tables),
            'byte_distinct_tables':len({x['sha256']for x in tables}),
            'parsed_distinct_tables':len({x['parsed_sha256']for x in tables}),
            'state_counts_including_rejected_controls':dict(sorted(collections.Counter(x['states']for x in tables).items())),
            'unparsable':bad,'archives':list(seen.values()),'tables':tables}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('tables','archives')},indent=2))


if __name__=='__main__':main()
