#!/usr/bin/env python3
"""Read-only exact current-port and selected-leader check for the proposal."""
import gzip,hashlib,json,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
HERE=Path(__file__).resolve().parent
P=HERE.parent/'thirteen-second-first-norm-corrections'
G=P/'polynomial88.json'
PIN='32d896933d3f3a524adfad130bacddd5cb137bfe9438e62dfcfec570a8c0e8e1'
def require(ok,message):
    if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
raw=G.read_bytes();require(sha(raw)==PIN,'actual parent graph pin')
g=json.loads(raw); records={};vals={}
for key,spec in g['coefficient_binding']['ports'].items():
    path=P/g['coefficient_binding']['path']/spec['file']
    blob=path.read_bytes();data=gzip.decompress(blob)
    require(sha(blob)==spec['gzip_sha256'] and sha(data)==spec['raw_sha256'],'entire port bytes')
    n=int.from_bytes(data,'big');require(n.bit_length()==spec['bits'],'bit length and endian')
    vals[key]=n;records[key]={'gzip_sha256':sha(blob),'raw_sha256':sha(data),'raw_bytes':len(data),'bits':n.bit_length()}
require(vals['beta']>0,'actual beta positive')
selected=64*vals['beta']**27
require(selected>0 and selected**2==4096*vals['beta']**54,'actual selected auxiliary/output coefficients nonzero')
require(sum(x['raw_bytes']for x in records.values())==47313,'complete tuple size')
print(json.dumps({'scope':'Proposal-only full current tuple and selected nonzero coefficient; no per-gate audit',
 'script_sha256':sha(Path(__file__).read_bytes()),'parent_graph_sha256':PIN,
 'ports':records,'raw_total_bytes':47313,
 'selected_auxiliary_coefficient':'64*beta^27','selected_output_coefficient':'4096*beta^54',
 'auxiliary_coefficient_positive':True,'output_coefficient_positive':True,
 'auxiliary_coefficient_bits':selected.bit_length()},indent=2))
