"""Read-only independent dossier verifier. Inspect, then run with python3 -I -S -B
verify_dossier.py EXPECTED_DOSSIER_MANIFEST_SHA256. The pin must be external.
"""
from pathlib import Path
import hashlib,json,stat,sys
ROOT=Path(__file__).absolute().parent
MANIFEST='DOSSIER_MANIFEST.json'
def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def inventory():
    result={'files':{},'directories':{}}
    for p in sorted(ROOT.rglob('*')):
        s=p.lstat();name=p.relative_to(ROOT).as_posix()
        require(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode),'Nonregular dossier entry')
        row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
        if stat.S_ISDIR(s.st_mode):result['directories'][name]=row
        elif name!=MANIFEST:
            require(s.st_nlink==1,'Hardlinked dossier entry');data=p.read_bytes();row.update(bytes=len(data),sha256=sha(data));result['files'][name]=row
    return result
if __name__=='__main__':
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize,'Use -I -S -B without optimization')
    require(len(sys.argv)==2,'Supply external manifest SHA-256')
    for p in [ROOT,*ROOT.parents]:require(not p.is_symlink(),'Symlink root path')
    mp=ROOT/MANIFEST;require(mp.is_file() and not mp.is_symlink() and mp.stat().st_nlink==1,'Invalid manifest file')
    raw=mp.read_bytes();require(sha(raw)==sys.argv[1],'Manifest pin mismatch')
    manifest=json.loads(raw);require(manifest.get('format')=='Independent Report67 release-review dossier v1','Wrong dossier schema')
    require(inventory()=={k:manifest[k] for k in ('files','directories')},'Dossier bytes/inventory/modes/mtime mismatch')
    print(json.dumps({'status':'PASS','files':len(manifest['files']),'manifest_sha256':sys.argv[1]}))
