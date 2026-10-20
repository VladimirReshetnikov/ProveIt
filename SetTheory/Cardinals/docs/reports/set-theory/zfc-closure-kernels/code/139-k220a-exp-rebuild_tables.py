#!/usr/bin/env python3
"""Reconstruct exploratory table bytes only. This is not a correctness checker."""
from pathlib import Path
from io import BytesIO
import argparse,hashlib,json,zipfile
R=Path(__file__).resolve().parents[1]
def need(x,m):
 if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',required=True,type=Path);a=p.parse_args();out=a.output_dir.resolve()
need(out!=R and R not in out.parents,'Output must be outside packet');need(not out.exists()or not any(out.iterdir()),'Output must be empty');out.mkdir(parents=True,exist_ok=True)
archive=(R/'vendor/K220_Construction_2026-10-20.zip').read_bytes()
need(sha(archive)=='132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00','Wrong baseline archive')
with zipfile.ZipFile(BytesIO(archive))as z:raw=z.read('K220_Construction_2026-10-20/machine/k220.native.tm')
B={(int(v[0]),int(v[1])):[int(v[2]),v[3],int(v[4])] for l in raw.decode().splitlines() if l and not l.startswith('#') for v in[l.split()]}
records=[]
for entry in json.loads((R/'exploratory/selection.json').read_text())['selected']:
 folder=R/'exploratory'/entry['label'];recipe=json.loads((folder/'table_recipe.json').read_text());need(sha(raw)==recipe['baseline_native_sha256'],'Recipe baseline differs');T=dict(B)
 for patch in recipe['row_patches']:
  k=patch['state'],patch['read'];need(T[k]==patch['old'],'Unexpected old row');T[k]=patch['new']
 encoded=('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')
 need(sha(encoded)==recipe['output_sha256'] and encoded==(folder/'candidate.tm').read_bytes(),'Table reconstruction differs')
 need(sha((folder/'sites.json').read_bytes())==recipe['source_sha256'],'Supplied source differs')
 (out/(entry['label']+'.tm')).write_bytes(encoded);records.append({'label':entry['label'],'table_sha256':sha(encoded),'source_sha256':recipe['source_sha256'],'working_states':len({q for q,b in T}),'semantic_proof':False})
receipt={'status':'EXPLORATORY_TABLE_BYTES_RECONSTRUCTED_ONLY','records':records,'scope':'No source-equivalence, unbounded runtime, or consistency proof is asserted.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
