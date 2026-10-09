"""Check exact kernel identity in a supplied local directory; never fetch or edit."""
import argparse
from hashlib import sha1,sha256
import json
from pathlib import Path

PINS={'interval_orbits.py':'e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8',
      'interval_orbit_verify.py':'0ccb56a0e8b5f1255384121d7417441314727720'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel-dir',type=Path,required=True)
    args=parser.parse_args();rows=[];ok=True
    for name,expected in PINS.items():
        path=args.kernel_dir/name
        if not path.is_file():
            rows.append(dict(file=name,match=False,error='missing file'));ok=False;continue
        data=path.read_bytes()
        actual=sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        match=actual==expected;ok &= match
        rows.append(dict(file=name,bytes=len(data),git_blob=actual,expected=expected,
                         sha256=sha256(data).hexdigest(),match=match))
    print(json.dumps(dict(all_match=ok,files=rows),indent=2))
    return 0 if ok else 1

if __name__=='__main__':raise SystemExit(main())
