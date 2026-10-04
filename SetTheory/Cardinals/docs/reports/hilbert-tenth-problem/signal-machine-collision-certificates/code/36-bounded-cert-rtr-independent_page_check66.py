#!/usr/bin/env python3
"""Independent raw-PNG and original article/tool metadata checks; no reviewed module imported."""
import hashlib,json,pathlib,stat,struct,zlib
D=pathlib.Path('/workspace/shared/report66-release-tools-independent-review-20261004'); inventories={}
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
for folder in ('article-locked-replay','article-relocated-locked-replay'):
    images={}
    for p in sorted((D/folder/'pages').glob('*.png')):
        data=p.read_bytes();assert data[:8]==b'\x89PNG\r\n\x1a\n';pos=8;parts=[];size=None;seen=[]
        while pos<len(data):
            n=int.from_bytes(data[pos:pos+4],'big');kind=data[pos+4:pos+8];payload=data[pos+8:pos+8+n]
            stored=int.from_bytes(data[pos+8+n:pos+12+n],'big');assert zlib.crc32(kind+payload)&0xffffffff==stored
            if kind==b'IHDR':size=struct.unpack('>IIBBBBB',payload);assert size[2:]==(8,2,0,0,0)
            if kind==b'IDAT':parts.append(payload)
            seen.append(kind);pos+=n+12
        assert pos==len(data) and seen[0]==b'IHDR' and seen[-1]==b'IEND'
        width,height=size[:2];decoder=zlib.decompressobj();raster=decoder.decompress(b''.join(parts))
        assert decoder.eof and not decoder.unused_data and len(raster)==height*(1+3*width)
        assert all(raster[k*(1+3*width)]<=4 for k in range(height))
        images[p.name]={'width':width,'height':height,'sha256':sha(data),'bytes':len(data)}
    assert len(images)==21 and images==json.loads((D/folder/'PAGE_INVENTORY.json').read_bytes())
    inventories[folder]=images
assert inventories['article-locked-replay']==inventories['article-relocated-locked-replay']
save(D/'INDEPENDENT_PAGE_CHECKS.json',{'status':'PASS','page_count_per_replay':21,'both_render_inventories_identical':True,'checks':'Independent PNG chunk CRC, RGB8 noninterlaced dimensions, complete zlib stream, decoded raster size, filter bytes, and equality to reported inventories','pages':inventories})
original=pathlib.Path('/workspace/shared/report66-bounded-certificates-counting-release-20261004');candidate=D/'article-candidate'
def entry(p):
    s=p.lstat();row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'type':stat.S_IFMT(s.st_mode)}
    if p.is_file():row.update(sha256=sha(p.read_bytes()),bytes=s.st_size)
    return row
report={}
for name in ('Report66.pdf','Report66.tex','INPUT_PINS.json','manuscript','tools'):
    names=[name]+([str(p.relative_to(original)) for p in sorted((original/name).rglob('*'))] if (original/name).is_dir() else [])
    for rel in names:
        left,right=entry(original/rel),entry(candidate/rel);assert left==right,rel;report[rel]=left
save(D/'ARTICLE_AND_TOOL_PRESERVATION.json',{'status':'PASS','basis':'Final original article, input-map, manuscript and tool bytes/modes/nanosecond mtimes equal the copy2 metadata snapshot taken before reviewer replay; includes manuscript/tools directory metadata. Original outer release root and README are excluded because the author was concurrently making the authorized README qualification.','entries':report})
print('PASS: 42 PNG rasters, identical page inventories, original article/tool metadata preserved')
