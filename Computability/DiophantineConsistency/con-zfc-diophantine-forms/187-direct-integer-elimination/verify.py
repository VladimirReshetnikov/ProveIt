#!/usr/bin/env python3
"""Verify pinned inputs, arithmetic certificates, printed definitions and series.

These are finite algebra and artifact checks. The ordinary unbounded proof
and inherited C222/ZF/ZFC calibration are identified separately in PROOF.md
and the manuscript.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
PINNED={
 'source/anchor219.json':'507ffcdf7d90ef5e892c62b0e35139453de8f02ed482e9f17c14d92cbacb2cfb',
 'source/anchor219_certificate.json':'10469ed4a7d40f163fd026ee8b2131e96d8bf4c777ae0acd202e6a224f6aa22d',
 'joint209.json':'9bd9f942016c0966b7b73c82fe4ecf394732ebecfd2469484429f7294fde9156',
}

def main():
    for name,expected in PINNED.items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('Pinned source changed: '+name)
    for row in json.loads((ROOT/'source/PINNED_INPUTS.json').read_text()):
        exact=(ROOT/row['exact_upstream_file']).read_bytes()
        working=(ROOT/row['working_file']).read_bytes()
        if working!=exact+b'\n':raise ValueError('Unexpected source normalization')
        sha=hashlib.sha1(b'blob '+str(len(exact)).encode()+b'\0'+exact).hexdigest()
        if sha!=row['github_blob_sha']:raise ValueError('Pinned GitHub blob mismatch')
    checks=[
        'code/verify_joint.py',
        'code/verify_projection.py',
        'code/verify_report.py',
        'research/affine_center_obstruction/verify_series.py',
    ]
    reports=[]
    for check in checks:
        result=subprocess.run([sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(ROOT/check)],capture_output=True,text=True,check=True)
        parsed=json.loads(result.stdout)
        if parsed.get('status')!='PASS':raise ValueError('Subcheck did not pass: '+check)
        reports.append({'check':check,'status':'PASS','details':parsed})
    print(json.dumps({'status':'PASS','checks':reports,'source':'pinned and exact polynomial source bindings','semantic_scope':'ordinary proof in PROOF.md; inherited C222/ZF/ZFC calibration'}))
if __name__=='__main__':main()
