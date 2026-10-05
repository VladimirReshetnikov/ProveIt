#!/usr/bin/env python3
"""Fresh immutable ZIP/hash/span triage; no archived program execution/import.

The only new mathematical diagnostics are a permutation determinant from the
printed recurrence and finite factorial identities. They do not replay either
report's checker or certify its infinite theorems.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from io import BytesIO
from itertools import permutations
import json
from math import factorial
from pathlib import Path, PurePosixPath
import subprocess
import zipfile

COMMIT = 'e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9'
BASES = ('A279619_Hankel_Positivity', 'Zero_Bias_Occupancy_Research_Package')
READS = {
 'A279619_Hankel_Positivity/README.md': 'full',
 'A279619_Hankel_Positivity/SOURCE_AUDIT.md': 'full',
 'A279619_Hankel_Positivity/OEIS_NOTE.txt': 'full',
 'A279619_Hankel_Positivity/SHA256SUMS.txt': 'full',
 'A279619_Hankel_Positivity/article.tex': [(50,230),(293,348),(441,663),(761,777),(850,873),(1045,1289),(1329,1355)],
 'A279619_Hankel_Positivity/code/verify_certificates.py': 'full',
 'A279619_Hankel_Positivity/data/validation.json': 'full',
 'occupancy_research/README.txt': 'full',
 'occupancy_research/numeric_notes.txt': 'full',
 'occupancy_research/occupancy_article.tex': [(55,365),(605,718),(1502,1882)],
 'occupancy_research/verify_occupancy.py': [(1,100),(522,548),(665,699)],
 'occupancy_research/data/verification_summary.json': 'full',
}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def git(repo, *args):
    return subprocess.check_output(['git','-C',str(repo),*args])

def digest(data):
    return sha256(data).hexdigest()

def inspect(repo):
    result = {'commit': COMMIT, 'archives': [], 'execution_boundary': 'No supplied, archived, frozen, or predecessor program executed or imported. No build/PDF inspection.', 'read_span_convention': 'Inclusive lines; SHA-256 on original byte lines with original line endings.'}
    all_data = {}
    for base in BASES:
        path = 'docs/incoming/' + base + '.zip'
        raw = git(repo, 'show', COMMIT + ':' + path)
        archive = zipfile.ZipFile(BytesIO(raw))
        require(archive.testzip() is None, 'ZIP CRC failed')
        infos = archive.infolist()
        names = [i.filename for i in infos]
        require(len(names)==len(set(names)), 'duplicate member path')
        for info in infos:
            parts = PurePosixPath(info.filename)
            require(not parts.is_absolute() and '..' not in parts.parts, 'unsafe path')
            require(((info.external_attr >> 16) & 0o170000) != 0o120000, 'symlink')
        obj = {'path': path, 'commit': COMMIT, 'blob': git(repo,'rev-parse',COMMIT+':'+path).decode().strip(), 'bytes':len(raw), 'sha256':digest(raw), 'crc_valid':True, 'safe_unique_paths':True, 'members':[]}
        for info in infos:
            if info.is_dir():
                continue
            data = archive.read(info)
            all_data[info.filename] = data
            member = {'path':info.filename,'bytes':len(data),'sha256':digest(data),'coverage':'hash only'}
            if info.filename.endswith('/data/certificates.json'):
                member['coverage']='all JSON parsed for rational coefficient shape/sign/count only; defining identities not replayed'
            if info.filename in READS:
                lines = data.splitlines(keepends=True)
                ranges = READS[info.filename]
                if ranges == 'full':
                    ranges = [(1,len(lines))]
                member['line_count'] = len(lines)
                member['read_spans'] = []
                for lo,hi in ranges:
                    require(1<=lo<=hi<=len(lines), 'span outside member '+info.filename)
                    block = b''.join(lines[lo-1:hi])
                    member['read_spans'].append({'start_line':lo,'end_line':hi,'bytes':len(block),'sha256':digest(block)})
                member['coverage'] = 'full inert text read' if READS[info.filename]=='full' else 'selected inert text spans'
            obj['members'].append(member)
        obj['regular_member_count'] = len(obj['members'])
        manifests = [i.filename for i in infos if PurePosixPath(i.filename).name.startswith('SHA256SUMS')]
        obj['internal_manifests'] = []
        for name in manifests:
            checks = []
            parent = str(PurePosixPath(name).parent)
            for line in archive.read(name).decode().splitlines():
                expected, rel = line.split(None,1)
                rel = rel.lstrip('*')
                target = parent+'/'+rel
                require(target in names, 'manifest target missing')
                actual = digest(archive.read(target))
                require(expected==actual, 'manifest mismatch '+target)
                checks.append({'path':target,'sha256':actual})
            obj['internal_manifests'].append({'path':name,'entries':checks,'all_match':True})
        result['archives'].append(obj)
    cert=json.loads(all_data['A279619_Hankel_Positivity/data/certificates.json'])
    coeffs=cert['polynomials']
    require(len(coeffs)==21,'polynomial count')
    count=0
    for v in coeffs.values():
        require(v['degree']+1==len(v['coefficients']) and v['shift']==5,'coefficient shape')
        require(Fraction(v['scale'])>0 and all(int(c)>0 for c in v['coefficients']),'coefficient positivity')
        count+=len(v['coefficients'])
    require(count==1090,'coefficient count')
    result['parsed_certificate_shape']={'polynomials':21,'positive_coefficients':count,'scope':'All records parsed as inert rational data; identities not replayed. This alone is not a TP5 proof.'}
    c=[Fraction(1),Fraction(2)]
    for n in range(1,11):
        c.append(((26*n*n+13*n+2)*c[-1]+(27*n*n-27*n+6)*c[-2])/((n+1)**2))
    det=Fraction(0)
    for p in permutations(range(6)):
        inversions=sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))
        term=Fraction((-1)**inversions)
        for i,j in enumerate(p):term*=c[1+i+j]
        det+=term
    require(det == -26875777009408537346562624,'D6(1) mismatch')
    checks=0
    for k in range(21):
        odd=1
        for j in range(1,2*k+2,2):odd*=j
        require(Fraction(2**k,factorial(2*k+1))==Fraction(1,factorial(k)*odd),'factorial identity')
        checks+=1
    result['fresh_small_math']={'method':'Independent six-by-six Leibniz permutation determinant (720 terms), not archived elimination; finite factorial checks only.','c_0_through_11':[str(v) for v in c],'D6_shift1':str(det),'factorial_identity_k_0_through_20':checks,'not_claimed':'No global TP5 replay, spectral repair proof, CLT/LDP proof, runtime/cost bound, or universal compiler certification.'}
    result['findings']={'nearby_substantive_error_found':False,'scope':'Bounded selected interfaces, not full proofs. Saved tests are source claims, not replayed.','relevance':'Finite rational recurrence/certificate and probability-conditioning methods; no Turing-complete substrate or paid ordinary-integer Diophantine compiler supplied in read interfaces.'}
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    data=inspect(a.repo)
    with a.output.open('x') as f:json.dump(data,f,indent=2);f.write('\n')
    print('PASS: 2 archives / 39 regular members; internal manifest and selected spans authenticated; scoped fresh diagnostics passed.')
if __name__=='__main__':main()
