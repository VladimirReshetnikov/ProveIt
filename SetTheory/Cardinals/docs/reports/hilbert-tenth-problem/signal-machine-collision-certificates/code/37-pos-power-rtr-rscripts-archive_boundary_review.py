"""Independent ZIP integrity and explicitly unauthenticated container-boundary probes."""
from pathlib import Path
import copy,json,runpy,struct,subprocess,sys,zipfile
BASE=Path('/workspace/shared/report67-release-independent-review-20261004')
I=runpy.run_path(str(BASE/'auth_snapshot.py'));inv,sha,enc=I['inventory'],I['sha'],I['encoded']
root=BASE/'sealed-candidate';pin=sha((root/'RELEASE_MANIFEST.json').read_bytes());before=inv(root);results=[]
def extract(name,archive,success,needle=None):
    output=BASE/(name+'-output')
    c=subprocess.run([sys.executable,'-I','-S','-B',str(root/'tools/release67.py'),'extract','--manifest-sha256',pin,'--archive',str(archive),'--output-dir',str(output)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (BASE/(name+'.stdout')).write_bytes(c.stdout)
    assert (c.returncode==0)==success,(name,c.stdout[-2000:])
    if needle:assert needle.encode() in c.stdout
    if not success:assert not output.exists()
    else:
        m=json.loads((root/'RELEASE_MANIFEST.json').read_bytes());i=inv(output)
        assert i['directories']==m['directories'] and {n:r for n,r in i['files'].items() if n!='RELEASE_MANIFEST.json'}==m['files']
    results.append({'name':name,'status':'PASS','exit_status':c.returncode})
archive=BASE/'container-variant.zip'
with zipfile.ZipFile(BASE/'candidate-a.zip') as zin,zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_STORED) as zout:
    zout.comment=b'Container metadata intentionally outside payload authentication.'
    for original in zin.infolist():
        i=copy.copy(original);i.date_time=(2001,2,3,4,5,6);i.compress_type=zipfile.ZIP_STORED;i.comment=b'non-authenticated entry comment';zout.writestr(i,zin.read(original))
extract('container-boundary-accept',archive,True)
with zipfile.ZipFile(archive) as z: offset=z.getinfo('Report67/README.md').header_offset
raw=bytearray(archive.read_bytes());namesize,extrasize=struct.unpack_from('<HH',raw,offset+26);data_offset=offset+30+namesize+extrasize;raw[data_offset]^=1
bad=BASE/'archive-corrupt-crc.zip';bad.write_bytes(raw);extract('archive-crc-reject',bad,False,'ZIP CRC failure')
bad=BASE/'archive-malformed.zip';bad.write_bytes(b'PK\x03\x04truncated');extract('archive-malformed-reject',bad,False)
assert inv(root)==before
receipt={'status':'PASS','scope':'Independent archive payload/container boundary test','tests':results,'source_preserved':True,'script_sha256':sha(Path(__file__).read_bytes())}
(BASE/'ARCHIVE_BOUNDARY_RECEIPT.json').write_bytes(enc(receipt));print(enc(receipt).decode())
