"""Independent inert snapshot/copy authentication; stdlib only, no input execution."""
from pathlib import Path
import hashlib,json,os,shutil,stat
BASE=Path('/workspace/shared/report67-release-independent-review-20261004')
SOURCE=Path('/workspace/shared/report67-power-reductions-release-20261004')
def sha(b): return hashlib.sha256(b).hexdigest()
def encoded(v): return (json.dumps(v,sort_keys=True,indent=2)+'\n').encode()
def inventory(root):
    out={'files':{},'directories':{}}
    s=root.lstat(); assert stat.S_ISDIR(s.st_mode)
    out['root']={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
    for p in sorted(root.rglob('*')):
        s=p.lstat(); n=p.relative_to(root).as_posix(); row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
        if stat.S_ISDIR(s.st_mode): out['directories'][n]=row
        else:
            assert stat.S_ISREG(s.st_mode) and s.st_nlink==1, n
            b=p.read_bytes(); assert len(b)==s.st_size
            row.update(bytes=len(b),sha256=sha(b)); out['files'][n]=row
    return out
if __name__=='__main__':
    before=inventory(SOURCE)
    expected={'Report67.pdf':'37005d94aa9a6037c35f64638a2443fdb471aff9cee8eb56c1529c32566fa58d','manuscript/MANUSCRIPT_PINS.json':'fae9d4bcd2e199f70a136f73ac42f22aa21e4c368ac6ff2c1878aa5640a00822','tools/BUILD_DEPENDENCIES_LOCK.json':'924a24fab30a2e05eccd168d7951273e31b99a8adbb3290ab5d8b6f332b884e1','INPUT_PINS.json':'a7061bc1c5b91c4f3940e06530b428f373ad42612c9a31372d7561a4607f8a6a'}
    assert all(before['files'][n]['sha256']==h for n,h in expected.items())
    origins=json.loads((SOURCE/'INPUT_PINS.json').read_text())['source_roots']
    originals={p:inventory(Path(p)) for p in sorted(set(origins.values()))}
    shutil.copytree(SOURCE,BASE/'candidate',copy_function=shutil.copy2)
    assert inventory(SOURCE)==before==inventory(BASE/'candidate')
    (BASE/'CANDIDATE_AUTHENTICATION.json').write_bytes(encoded({'status':'PASS','source':str(SOURCE),'expected_pins':expected,'source_and_copy_identical':True,'inventory':before}))
    (BASE/'ORIGINALS_BEFORE.json').write_bytes(encoded(originals))
    print(json.dumps({'status':'PASS','candidate_files':len(before['files']),'candidate_directories':len(before['directories']),'original_roots':len(originals),'authentication_sha256':sha((BASE/'CANDIDATE_AUTHENTICATION.json').read_bytes())}))
