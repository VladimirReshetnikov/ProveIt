#!/usr/bin/env python3
"""Read-only verification, external manifest generation and deterministic archive creation.
No scientific code is imported or executed. Invoke with python3 -I -S -B.
"""
import argparse,hashlib,json,os,stat,sys,zipfile
from pathlib import Path,PurePosixPath
ROOT=Path(__file__).resolve().parent.parent
PACKET='646de47472089e9909fafbf0ed1e1a7851a114d862e4df9b31d0802815772044'
AUDIT='327ac64f5df5f8dbd2929cdcbabb147a19198bdf9b23291edb948b726514bbbe'

def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(v):return json.dumps(v,sort_keys=True,indent=2)+'\n'
def safe_name(s):
    p=PurePosixPath(s);require(not p.is_absolute() and str(p)==s and s and all(x not in ('.','..','') for x in s.split('/')) and '\\' not in s,'Unsafe relative path');return s
def regular(p):
    t=p.lstat();require(stat.S_ISREG(t.st_mode) and t.st_nlink==1,'Expected regular single-link file: '+str(p));return p.read_bytes()
def inventory(base):
    require(base.is_dir() and not base.is_symlink(),'Expected real input directory')
    rows={}
    for p in sorted(base.rglob('*')):
        t=p.lstat();require(not stat.S_ISLNK(t.st_mode),'Input symlink rejected')
        if stat.S_ISDIR(t.st_mode):continue
        b=regular(p);rows[safe_name(p.relative_to(base).as_posix())]={'bytes':len(b),'sha256':sha(b)}
    return rows

def fresh_file(raw):
    require(raw.startswith('/') and not raw.startswith('//'),'Canonical absolute destination required')
    p=Path(raw);require(str(p)==raw and all(c not in ('.','..') for c in raw.split('/')),'Noncanonical destination')
    require(not os.path.lexists(p),'Destination already exists')
    require(p.parent.is_dir(),'Destination parent must exist')
    for q in [p.parent,*p.parent.parents]:require(not q.is_symlink(),'Symlink destination ancestor')
    require(ROOT not in p.parents and p!=ROOT and p not in ROOT.parents,'Destination must be outside release')
    return p

def check_inputs():
    b=regular(ROOT/'science/PACKET_MANIFEST.json');require(sha(b)==PACKET,'Frozen science manifest mismatch')
    m=json.loads(b);expected={}
    for r in m['files']:
        n=safe_name(r['path']);require(n not in expected,'Duplicate science entry');expected[n]={'bytes':r['bytes'],'sha256':r['sha256']}
    expected['PACKET_MANIFEST.json']={'bytes':len(b),'sha256':PACKET}
    require(len(expected)==60 and inventory(ROOT/'science')==expected,'Science inventory or byte mismatch')
    b=regular(ROOT/'independent-audit/AUDIT_RECEIPT.json');require(sha(b)==AUDIT,'Frozen audit receipt mismatch')
    rec=json.loads(b);expected=rec['audit_files'].copy()
    for n in expected:safe_name(n)
    expected['AUDIT_RECEIPT.json']={'bytes':len(b),'sha256':AUDIT}
    require(len(expected)==9 and inventory(ROOT/'independent-audit')==expected,'Audit inventory or byte mismatch')
    pins=json.loads(regular(ROOT/'science/SOURCE_PINS.json'))['read_only_dependencies'];dep={}
    for i,item in enumerate(pins,1):
        p=Path(item['path']);name=f'{i:02d}-'+p.parent.name+'-'+p.name;data=regular(ROOT/'dependencies'/name)
        require(sha(data)==item['sha256'],'Dependency mismatch: '+name);dep[name]={'bytes':len(data),'sha256':sha(data)}
    require(len(dep)==7 and inventory(ROOT/'dependencies')==dep,'Dependency inventory mismatch')
    for directory,pin,total in (
        ('real-input','20e4e23ea114e08ec961e0cf473617b06f85e15f00168cb1fe1e5f13e0d0a128',3),
        ('real-input-audit','f39d8e3ac359e8b4b8c63deb44e098f76c57f564639754390997e59832c4a0fe',6)):
        base=ROOT/directory;data=regular(base/'MANIFEST.sha256');require(sha(data)==pin,'Topology manifest mismatch')
        want={}
        for line in data.decode().splitlines():
            value,name=line.split('  ',1);safe_name(name);require(name not in want,'Duplicate topology path')
            b=regular(base/name);require(sha(b)==value,'Topology byte mismatch');want[name]={'sha256':value,'bytes':len(b)}
        want['MANIFEST.sha256']={'sha256':pin,'bytes':len(data)}
        require(len(want)==total and inventory(base)==want,'Topology inventory mismatch')
    require(inventory(ROOT/'real-input-dependencies')=={'GUARDS.txt':{'bytes':len(regular(ROOT/'real-input-dependencies/GUARDS.txt')),'sha256':'d8c1dec4945dd4f3dedfdf469d3b6e51ea9991e8234cccb1daf49c0d8cbc6ce9'}},'Topology guard dependency mismatch')
    mp=json.loads(regular(ROOT/'manuscript/MANUSCRIPT_PINS.json'))
    require(set(mp)=={'report59.tex','fixture-table.tex','geometry-figure.tex'},'Unexpected manuscript pin set')
    require(set(inventory(ROOT/'manuscript'))==set(mp)|{'MANUSCRIPT_PINS.json'},'Unexpected manuscript inventory')
    require(all(sha(regular(ROOT/'manuscript'/n))==v for n,v in mp.items()),'Manuscript pin mismatch')
    return {'science_files':60,'audit_files':9,'dependency_files':7,'manuscript_sources':3,'topology_files':10,'scope':'Byte authentication only; no scientific executable'}

def check_manifest(expected_hash):
    b=regular(ROOT/'MANIFEST.json');require(sha(b)==expected_hash,'Release manifest pin mismatch');m=json.loads(b)
    require(m['format']=='report59-release-manifest-v1','Unknown manifest format')
    rows=inventory(ROOT);del rows['MANIFEST.json']
    require(rows==m['files'],'Release inventory or hash mismatch');check_inputs();return m

def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize,'Use python3 -I -S -B without optimization')
    ap=argparse.ArgumentParser(description=__doc__);sp=ap.add_subparsers(dest='action',required=True)
    sp.add_parser('check-inputs')
    p=sp.add_parser('manifest');p.add_argument('--output',required=True)
    p=sp.add_parser('verify');p.add_argument('--manifest-sha256',required=True)
    p=sp.add_parser('archive');p.add_argument('--manifest-sha256',required=True);p.add_argument('--output',required=True)
    a=ap.parse_args()
    if a.action=='check-inputs':print(encode({'status':'PASS',**check_inputs()}));return
    if a.action=='manifest':
        check_inputs();out=fresh_file(a.output);rows=inventory(ROOT);rows.pop('MANIFEST.json',None)
        data=encode({'format':'report59-release-manifest-v1','files':rows}).encode();out.write_bytes(data)
        print(encode({'status':'PASS','manifest_sha256':sha(data),'files':len(rows),'output':str(out)}));return
    m=check_manifest(a.manifest_sha256)
    if a.action=='verify':print(encode({'status':'PASS','manifest_sha256':a.manifest_sha256,'files':len(m['files'])+1}));return
    out=fresh_file(a.output);before=inventory(ROOT)
    try:
        with out.open('xb') as stream:
            with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
                for name in sorted(before):
                    data=regular(ROOT/name);require(sha(data)==before[name]['sha256'],'Source changed while archiving')
                    info=zipfile.ZipInfo(name,date_time=(2026,10,4,0,0,0));info.create_system=3;info.external_attr=(stat.S_IFREG|0o444)<<16;info.compress_type=zipfile.ZIP_DEFLATED
                    z.writestr(info,data,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
        require(before==inventory(ROOT),'Release changed while archiving')
        with zipfile.ZipFile(out) as z:
            require(z.namelist()==sorted(before),'ZIP inventory mismatch')
            for n in z.namelist():require(sha(z.read(n))==before[n]['sha256'],'ZIP byte mismatch')
        print(encode({'status':'PASS','files':len(before),'zip_sha256':sha(regular(out)),'manifest_sha256':a.manifest_sha256,'inputs_preserved':True,'output':str(out)}))
    except BaseException:
        if out.exists():out.unlink()
        raise
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,zipfile.BadZipFile) as e:
        print('RELEASE REFUSED: '+str(e),file=sys.stderr);raise SystemExit(2)
