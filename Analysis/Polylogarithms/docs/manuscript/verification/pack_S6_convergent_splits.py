"""Stream generated exact rows into lossless sparse integer records and a joint matrix.

The raw JSON experiments remain in scratch. No incoming artifact is altered.
The compact encoding retains every input word and projected coefficient.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import array,gzip,hashlib,json,math,struct,sys,time
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1];V=B/'verification';S=V/'.scratch-real-orders'
C=B.parent/'reports/stieltjes-harmonic-resonance/continuations/exact-resonant-identities/certificates/cayley'
sys.path.insert(0,str(C/'code'))
import verify_complete_cayley as M
P=M.P
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):h.update(block)
    return h.hexdigest()
for name,h in M.EXPECTED_SHA256.items():assert sha(C/name)==h
coords=[w for w in product(range(5),repeat=7) if P.admissible(w) and P.depth(w)<=4 and P.parity(w)]
coords += [w for w in product(range(5),repeat=7) if P.admissible(w) and P.depth(w)==5 and P.parity(w)]
assert len(coords)==8786
index={w:i for i,w in enumerate(coords)}
def stream_rows(path):
    decoder=json.JSONDecoder();chunk=1<<20
    with gzip.open(path,'rt',encoding='utf-8') as f:
        buf='';prefix=''
        while True:
            buf+=f.read(chunk)
            at=buf.find('"rows":[')
            if at>=0:prefix=buf[:at]+'"rows":';buf=buf[at+8:];break
            assert len(buf)<chunk*2,'Missing rows marker'
        while True:
            buf=buf.lstrip()
            if not buf:
                buf=f.read(chunk);assert buf,'Truncated rows array';continue
            if buf[0]==']':
                # Parsing the reconstructed outer object validates every tail
                # token and binds its metadata without retaining the row array.
                metadata=json.loads(prefix+'[]'+buf[1:]+f.read())
                assert metadata['status']=='PASS'
                return
            if buf[0]==',':buf=buf[1:].lstrip()
            while True:
                try:item,end=decoder.raw_decode(buf);break
                except json.JSONDecodeError:
                    more=f.read(chunk);assert more,'Malformed/truncated row';buf+=more
            yield item
            buf=buf[end:]
entry=struct.Struct('<Hq');D=5760;NC=8786
packed=[]
for left in [2,3]:
    started=time.monotonic();stem=f'S6-split-{left}-{7-left}-depth-five'
    raw=S/(stem+'-probe.json.gz');meta=json.loads((S/(stem+'-probe-summary.json')).read_text())
    assert meta['status']=='PASS' and meta['tested_inputs']==3604 and sha(raw)==meta['compressed_records_sha256']
    target=V/(stem+'-sparse.bin.gz');nr=0;entries=0;maximum=0;seen=set();bounded=0;input_denominator=1
    logical=hashlib.sha256()
    with target.open('wb') as output:
        with gzip.GzipFile(filename='',mode='wb',fileobj=output,mtime=0) as out:
            out.write(struct.pack('<4sIIQ',b'S6S1',3604,NC,D))
            for row in stream_rows(raw):
                u=tuple(row['left_adapted_word']);w=tuple(row['input_adapted_word'])
                assert len(u)==left and len(w)==7-left and P.admissible(u) and P.admissible(w)
                assert P.depth(u)+P.depth(w)==5 and P.parity(u)!=P.parity(w)
                assert (u,w) not in seen;seen.add((u,w))
                sparse={};top=False
                for word,c in row['projected_relation']:
                    word=tuple(word);k=index[word];q=Fraction(c)
                    assert q and k not in sparse and D%q.denominator==0
                    input_denominator=math.lcm(input_denominator,q.denominator)
                    z=q.numerator*(D//q.denominator);assert -(1<<63)<z<(1<<63)
                    assert Fraction(z,D)==q
                    sparse[k]=z;top |= k>=2546;maximum=max(maximum,abs(z))
                assert len(sparse)==row['projected_support']
                assert (not top)==row['bounded_space_member']
                bounded+=not top
                data=bytearray(bytes([left,*u,*w])+struct.pack('<I',len(sparse)))
                for k,z in sorted(sparse.items()):
                    part=entry.pack(k,z);kk,zz=entry.unpack(part);assert (kk,zz)==(k,z)
                    data.extend(part)
                out.write(data);logical.update(data);entries+=len(sparse);nr+=1
                if nr%200==0:print('Lossless sparse packing',left,nr,'/',3604,flush=True)
    assert nr==3604 and bounded==meta['bounded_projected_rows']
    result=dict(status='PASS',length_split=[left,7-left],rows=nr,columns=NC,common_denominator=D,source_projected_denominator=input_denominator,entries=entries,maximum_absolute_integer=maximum,bounded_rows=bounded,original_json_sha256=meta['compressed_records_sha256'],compact_sha256=sha(target),logical_row_bytes_sha256=logical.hexdigest(),source_code_sha256=M.EXPECTED_SHA256,format='S6S1 little endian: header <4sIIQ>; each row has eight bytes [left length, seven input letters], uint32 count, then sorted (uint16 coordinate,int64 coefficient) pairs. Coordinates are F4 odd admissible weight seven lexicographically, followed by exact-depth-five coordinates. Divide coefficients by the header denominator.',scope='Lossless encoding checks every coefficient, input, support count, depth and round-trip integer pair. Raw generated JSON retained unchanged in scratch; no input coordinate discarded. This is evidence integrity, not rational target membership.',elapsed_seconds=round(time.monotonic()-started,3))
    (V/(stem+'-packing.json')).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');packed.append((target,result))
# Append both compact families to the previous full-coordinate matrix.
old=S/'S6-all-letters-depth-five-matrix.bin';oldmeta=json.loads((V/'S6-all-letters-depth-five-matrix.json').read_text())
assert sha(old)==oldmeta['matrix_sha256'] and sys.byteorder=='little'
matrix=S/'S6-convergent-splits-matrix.bin';maximum=oldmeta['maximum_absolute_integer'];new_rows=0
with old.open('rb') as source,matrix.open('wb') as dest:
    magic,nr,nc,den=struct.unpack('<4sIIQ',source.read(20));assert (magic,nr,nc,den)==(b'S6M1',9395,NC,D)
    dest.write(struct.pack('<4sIIQ',b'S6M1',16603,NC,D))
    remaining=nr*nc*8
    while remaining:
        data=source.read(min(1<<20,remaining));assert data;dest.write(data);remaining-=len(data)
    last=source.read(nc*8);assert len(last)==nc*8 and not source.read(1)
    for path,meta in packed:
        logical=hashlib.sha256()
        with gzip.open(path,'rb') as f:
            assert struct.unpack('<4sIIQ',f.read(20))==(b'S6S1',3604,NC,D)
            for r in range(3604):
                head=f.read(12);assert len(head)==12;count=struct.unpack('<I',head[8:])[0]
                data=f.read(count*10);assert len(data)==count*10
                logical.update(head+data);a=array.array('q',[0])*NC;previous=-1
                for k,z in entry.iter_unpack(data):
                    assert previous<k<NC and z;previous=k;a[k]=z
                    maximum=max(maximum,abs(z))
                a.tofile(dest);new_rows+=1
                if new_rows%500==0:print('Full-coordinate joint split rows',new_rows,'/',7208,flush=True)
            assert not f.read(1)
        assert logical.hexdigest()==meta['logical_row_bytes_sha256']
    dest.write(last)
assert new_rows==7208
result=dict(status='PASS',rows=16603,columns=NC,common_denominator=D,previous_rows=9395,new_convergent_rows=7208,length_splits=[[2,5],[3,4]],source_compact_sha256={p.name:m['compact_sha256'] for p,m in packed},previous_matrix_sha256=oldmeta['matrix_sha256'],maximum_absolute_integer=maximum,maximum_includes_target=True,matrix_sha256=sha(matrix),source_code_sha256=M.EXPECTED_SHA256,scope='All exact coefficient pairs independently read from the compact files and written into 8786 coordinates. The earlier target is copied with every outside zero retained. Native finite-field elimination is a separate diagnostic; rational reconstruction and exact residuals are required for any rational membership claim.')
(V/'S6-convergent-splits-matrix.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Lossless split packing and joint matrix PASS',flush=True)
