"""Explicitly seal a finished Report 25 release; never called by replay."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
import json
from verify_release import ROOT, MANIFEST, DIGEST, manifest_data, verify


def main():
    data = manifest_data(ROOT)
    raw = (json.dumps(data,indent=2)+'\n').encode('utf-8')
    (ROOT/MANIFEST).write_bytes(raw)
    (ROOT/DIGEST).write_text(sha256(raw).hexdigest()+'  '+MANIFEST+'\n',encoding='ascii')
    print(json.dumps(verify(ROOT),indent=2))


if __name__=='__main__':
    main()
