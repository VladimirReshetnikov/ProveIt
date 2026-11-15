#!/usr/bin/env python3
"""Replay all 193 blank starts of each of the 55 supplied diagnostic tables.

Requires Python 3 and a C++17 g++ compiler. Output goes to an external directory.
The bundled table index binds the inputs; no repository or network is needed.
"""
import argparse,collections,csv,hashlib,json,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',type=pathlib.Path,default=HERE/'audit193')
ap.add_argument('--output',type=pathlib.Path)
ap.add_argument('--compiler',default='g++')
a=ap.parse_args();out=a.output or pathlib.Path(tempfile.mkdtemp(prefix='pa193-screen-'))
out.mkdir(parents=True,exist_ok=True)
index=json.loads((a.input/'index.json').read_text());assert len(index)==55
paths=[]
for r in index:
    p=a.input/'tables'/r['file'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];paths.append(p)
exe=out/'screen193'
subprocess.run([a.compiler,'-O2','-std=c++17',str(HERE/'audit193.cpp'),'-o',str(exe)],check=True)
with (out/'all_starts.csv').open('w') as f:subprocess.run([str(exe),*map(str,paths)],stdout=f,check=True)
rows=list(csv.DictReader((out/'all_starts.csv').open()));counts=collections.Counter(r['status'] for r in rows)
assert len(rows)==55*193
summary={'pinned_commit':'d8d4fb10149d6a76a56e615a35648c8c32847cf4','graphs':55,'working_states_per_graph':193,'blank_starts':len(rows),
 'transition_cap_per_start':100000,'outcomes':dict(counts),'unresolved_capped_starts':[r for r in rows if r['status']=='LIMIT'],
 'ray_certificate':'At the reached configuration, read zero, next control equals current control, and the half-line ahead contains no ones; repeated identical moves continue forever even if writing ones behind the head.',
 'scope':'Finite literal halts and exact outward self-loop rays. LIMIT is unresolved by this screen; no general state-count lower bound follows.'}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
assert dict(counts)=={'HALT':112,'RAY':10499,'LIMIT':4}
print(json.dumps(summary,indent=2));print('Output:',out)
