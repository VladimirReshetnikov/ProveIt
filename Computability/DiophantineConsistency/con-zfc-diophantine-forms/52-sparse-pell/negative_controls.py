#!/usr/bin/env python3
"""Failure-path tests for the sealed release; changes only temporary copies."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile
if not __debug__ or sys.flags.optimize:raise SystemExit('REJECT optimized Python')
R=pathlib.Path(__file__).resolve().parent

def expect_fail(args,cwd,needle):
    p=subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode==0 or needle not in p.stdout:
        raise RuntimeError('Negative control did not reject as expected: '+repr(args)+'\n'+p.stdout)
    return {'case':needle,'exit_code':p.returncode}

def main():
    rows=[];env=os.environ.copy()
    for flag in ['-O','-OO']:
        rows.append(expect_fail([sys.executable,flag,str(R/'verify_release.py'),'--integrity-only'],R,'REJECT'))
    with tempfile.TemporaryDirectory(prefix='proveit-negative-controls-') as td:
        d=pathlib.Path(td)/'release';shutil.copytree(R,d)
        target=d/'coefficients/beta.bin';raw=target.read_bytes();target.write_bytes(bytes([raw[0]^1])+raw[1:])
        rows.append(expect_fail([sys.executable,str(d/'verify_release.py'),'--integrity-only'],d,'HASH FAILURE'))
        target.write_bytes(raw);extra=d/'unexpected.tmp';extra.write_text('unexpected')
        rows.append(expect_fail([sys.executable,str(d/'verify_release.py'),'--integrity-only'],d,'FILE SET FAILURE'))
        extra.unlink();target.unlink()
        rows.append(expect_fail([sys.executable,str(d/'verify_release.py'),'--integrity-only'],d,'FILE SET FAILURE'))
        target.write_bytes(raw)
        cert=d/'packing/CERTIFICATE_174_interior_packed.json';obj=json.loads(cert.read_text())
        obj['weights'][1]=obj['weights'][0];cert.write_text(json.dumps(obj))
        rows.append(expect_fail([sys.executable,str(d/'packing/verify_certificate.py'),str(cert)],d,'AssertionError'))
        # Rehashing a corrupted provenance file does not evade its Git blob check.
        source=d/'review/postpin/STATUS.md';source.write_bytes(source.read_bytes()+b'\ncorrupt\n')
        hashes=json.loads((d/'RELEASE_HASHES.json').read_text())
        for p in [cert,source]:hashes[p.relative_to(d).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
        (d/'RELEASE_HASHES.json').write_text(json.dumps(hashes))
        rows.append(expect_fail([sys.executable,str(d/'verify_release.py'),'--integrity-only'],d,'SOURCE BLOB FAILURE'))
    print(json.dumps({'status':'PASS','negative_controls':rows},indent=2))
if __name__=='__main__':main()
