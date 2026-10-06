"""Write a deterministic ZIP from the closed, verified bundle inventory."""
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,json,zipfile,io,os,stat
from pathlib import Path
from check import FILES,ROOT,integrity,require
from safe_output import preflight,write_new

def seal(root=ROOT):
    entries=list(root.iterdir())
    require({p.name for p in entries} in [FILES,FILES-{'MANIFEST.json'}],'cannot seal an unexpected inventory')
    require(all(stat.S_ISREG(p.lstat().st_mode) for p in entries),'cannot seal nonregular entries')
    data={name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sorted(FILES-{'MANIFEST.json'})}
    encoded=(json.dumps(data,indent=2,sort_keys=True)+'\n').encode()
    fd=os.open(root/'MANIFEST.json',os.O_WRONLY|os.O_CREAT|os.O_TRUNC|os.O_NOFOLLOW,0o644)
    with os.fdopen(fd,'wb') as output:output.write(encoded)

def pack(destination):
    destination=preflight(destination,ROOT)
    integrity()
    buffer=io.BytesIO()
    with zipfile.ZipFile(buffer,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for name in sorted(FILES):
            info=zipfile.ZipInfo('Report132_bundle/'+name,(2026,10,2,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
            z.writestr(info,(ROOT/name).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    write_new(destination,buffer.getvalue(),ROOT)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seal',action='store_true',help='maintainer action after intentional changes, not verification')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    if args.output:preflight(args.output,ROOT)
    if args.seal:seal()
    if args.output:pack(args.output)
    if not args.seal and not args.output:p.error('specify --seal or --output')
if __name__=='__main__':main()
