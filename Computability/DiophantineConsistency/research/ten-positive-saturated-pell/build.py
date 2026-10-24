#!/usr/bin/env python3
"""Inert, hash-pinned materialization of four reviewed equations; executes no archive code."""
import argparse
from hashlib import sha256
import io,json,subprocess,sys,zipfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(data):return sha256(data).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole immutable dependency '+name)
    ap=pins['archive'];p=ROOT.parents[1]/ap['path']
    blob=p.read_bytes() if p.exists() else subprocess.check_output(['git','show',ap['commit']+':'+ap['path']],cwd=ROOT.parents[1])
    need(digest(blob)==ap['sha256'] and len(blob)==ap['bytes'],'complete pinned incoming Git/working-tree archive')
    archive=zipfile.ZipFile(io.BytesIO(blob));prefix=ap['root'];inventory=json.loads((HERE/'INCOMING_MEMBERS.json').read_bytes())
    need(set(inventory)==set(n.filename for n in archive.infolist() if not n.is_dir()),'complete archive member inventory')
    for name,pin in inventory.items():
        data=archive.read(name);need(digest(data)==pin['sha256'] and len(data)==pin['bytes'],'whole incoming member '+name)
    artifacts={}
    for name in ['saturated_upper','saturated_sharp','direct_saturated_upper','direct_saturated_sharp']:
        artifacts[name+'.json']=archive.read(prefix+'equations/'+name+'.json')
    for name in ['K','MC','MF_source','beta']:
        artifacts['coefficients/compact44_bfs/'+name+'.bin.gz']=archive.read(prefix+'coefficients/compact44_bfs/'+name+'.bin.gz')
    for name in ['saturation_semantics','saturated_degree_proof','complete_constants']:
        artifacts['source/'+name+'.tex']=archive.read(prefix+'report_parts/'+name+'.tex')
    artifacts['source/INCOMING_SOURCE_PINS.json']=archive.read(prefix+'SOURCE_PINS.json')
    for mode in ['', '_OPTIMIZED']:
        artifacts['REVIEWED_INCOMING_VERIFICATION'+mode+'.json']=archive.read(prefix+'checks/VERIFICATION'+mode+'.json')
    indexed=ROOT/'research/indexed-tile-enumeration';binding=json.loads((indexed/'coefficients/BINDING.json').read_bytes());binding['path']='coefficients/indexed_bfs/'
    artifacts['INDEXED_BINDING.json']=(json.dumps(binding,indent=2,sort_keys=True)+'\n').encode()
    for pin in binding['ports'].values():artifacts['coefficients/indexed_bfs/'+pin['file']]=(indexed/'coefficients'/pin['file']).read_bytes()
    for name,data in artifacts.items():
        target=HERE/name
        if args.check:need(target.read_bytes()==data,'deterministic entire generated member '+name)
        else:
            need(not target.exists() or target.read_bytes()==data,'refuse changed generated member overwrite '+name);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),check_mode=args.check,artifacts={n:digest(b) for n,b in artifacts.items()},incoming_or_parent_code_executed=False),indent=2,sort_keys=True))
if __name__=='__main__':main()
