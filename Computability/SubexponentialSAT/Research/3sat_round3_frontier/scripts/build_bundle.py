#!/usr/bin/env python3
"""Deterministically package an explicit allowlist, never arbitrary workspace files."""
import argparse,hashlib,json,pathlib,zipfile
R=pathlib.Path(__file__).resolve().parent.parent
p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=pathlib.Path);a=p.parse_args()
names=json.loads((R/'scripts/bundle_allowlist.json').read_text())
if len(names)!=len(set(names)):raise ValueError('duplicate allowlist')
data={n:(R/n).read_bytes() for n in sorted(names)}
manifest={'format':1,'source_pin':'474ddba696a5d385c091c23fb2995f69edd13e00',
 'scope':'Relative normalized contraction refinements and exact component improvements; no smaller SAT logarithmic order or full solver.',
 'files':{n:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in data.items()}}
data['MANIFEST.sha256.json']=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
a.output.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(a.output,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for n,b in sorted(data.items()):
        i=zipfile.ZipInfo(n,(2026,10,27,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,b)
b=a.output.read_bytes()
if len(b)>=4_000_000:raise ValueError('archive must be below4MB')
print(json.dumps({'archive':str(a.output),'bytes':len(b),'entries':len(data),'sha256':hashlib.sha256(b).hexdigest()},indent=2))
