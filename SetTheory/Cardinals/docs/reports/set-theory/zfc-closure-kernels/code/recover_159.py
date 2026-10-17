#!/usr/bin/env python3
"""Recover the available source56 payload from its committed incomplete ZIP.

Only complete local entries are accepted. A recovered entry does not imply that
all intended archive members were delivered. No checksum manifest is checked,
no missing source is fabricated, and no delivered code is executed.
"""
from pathlib import Path, PurePosixPath
import argparse,json,struct,subprocess,zlib

ARRIVAL='80e26b89e905bf3e5dfc322befdc1c6eaf25a109'
ARCHIVE='docs/incoming/zfc-state-reduction-research.zip'
HOST=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')

def members(raw):
    pos=0;result={}
    while pos<len(raw):
        if len(raw)-pos<30 or raw[pos:pos+4]!=b'PK\x03\x04':
            raise ValueError(f'Incomplete or unsupported local header at {pos}')
        _,version,flags,method,mtime,mdate,crc,csize,usize,nlen,xlen=struct.unpack_from('<4s5H3I2H',raw,pos)
        if flags&9:raise ValueError('Encrypted entries or data descriptors are unsupported')
        start=pos+30+nlen+xlen
        if start+csize>len(raw):raise ValueError('Incomplete local payload')
        name=raw[pos+30:pos+30+nlen].decode('utf-8' if flags&0x800 else 'cp437')
        rel=PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or '\\' in name:raise ValueError('Unsafe archive member')
        if name in result:raise ValueError('Duplicate archive member')
        data=raw[start:start+csize]
        if method==8:
            decoder=zlib.decompressobj(-15);data=decoder.decompress(data)+decoder.flush()
            if not decoder.eof or decoder.unused_data or decoder.unconsumed_tail:raise ValueError('Incomplete deflate stream')
        elif method!=0:raise ValueError('Unsupported compression method')
        if len(data)!=usize:raise ValueError('Local payload length mismatch')
        if not name.endswith('/'):result[name]=data
        pos=start+csize
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=Path.cwd())
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--map',type=Path)
    a=p.parse_args();repo=a.repo.resolve();out=a.output.resolve()
    if out.is_relative_to(repo) or out.exists():p.error('Use a new output directory outside the checkout')
    mapping=json.loads((a.map or repo/HOST/'data/intake-159-placement.json').read_text())
    raw=subprocess.check_output(['git','show',ARRIVAL+':'+ARCHIVE],cwd=repo)
    recovered=members(raw);prefix='zfc-state-reduction-research/'
    assert len(recovered)==327 and all(n.startswith(prefix) for n in recovered)
    originals={n[len(prefix):]:b for n,b in recovered.items()}
    placed=mapping['placements'];assert len(placed)==321
    for r in placed:
        if (repo/r['target']).read_bytes()!=originals[r['delivered']]:raise ValueError('Placed ancillary differs: '+r['target'])
    out.mkdir(parents=True)
    for n,b in recovered.items():
        f=out/n;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
    report={'status':'PARTIAL_DELIVERY_SALVAGED','arrival':ARRIVAL,'archive':ARCHIVE,'complete_local_members':327,'placed_ancillary_pairs_compared':321,'archive_only_members':6,'central_directory_present':False,'all_delivered_local_payloads_complete':True,'intended_package_complete':False,'missing_material':['work/theory_audit/','state89/92/98 degree-two summaries and journals','state82 degree-two journal'],'package_root':str(out/prefix),'scope':'Recovery only; no manifest check, delivered-code execution, proof or complete search claim.'}
    (out/'recovery.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
