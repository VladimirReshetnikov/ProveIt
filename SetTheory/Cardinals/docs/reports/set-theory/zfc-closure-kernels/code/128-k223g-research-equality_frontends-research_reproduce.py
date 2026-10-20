#!/usr/bin/env python3
"""Reproduce all nine exploratory logical proof artifacts using only scripts.

No retained proof JSON or receipt JSON is read as an input. This driver
copies its five companion scripts into --output-dir, runs each specified
mode in a fresh Python process, and checks the generated proof hashes
against the retained values embedded below. Python 3.9+; standard library.
"""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys

SCRIPTS=(
    'combined_helper_certificate.py',
    'crossed_box_helper_certificate.py',
    'specialization_crossed_helper_certificate.py',
    'gated_crossed_helper_certificate.py',
    'canonical_crossed_helper_certificate.py',
)
# (mode name, script, arguments, output stem, retained proof SHA256)
CASES=(
    ('combined','combined_helper_certificate.py',(),
     'combined_helper','be57c920653570325ee3764ceec429906d98af32d631072c9d089fc402e12571'),
    ('c2_rel','crossed_box_helper_certificate.py',('--kappa','rel'),
     'crossed_box_rel','dbfe5fb6e58d40b4617f7711de9bea10f07e553cfb264a6a41969b5dde9d252c'),
    ('c2_sum','crossed_box_helper_certificate.py',('--kappa','sum'),
     'crossed_box_sum','35aed4b1e62344876901288b700707d9ea35b113a71cddd32537700030b3a8a6'),
    ('specialization_c1','specialization_crossed_helper_certificate.py',(),
     'specialization_crossed_helper','f0b1337b25f61ab6f151cfa9d9a8c57f4f6cf83abfa3b8b1174c397e0d6c1e49'),
    ('gated_c1','gated_crossed_helper_certificate.py',(),
     'gated_crossed_helper','a1710661e69b05fbd4e537c4d8a7257a968c625b7d7af4e80471bea9d1f88531'),
    ('canonical_rel','canonical_crossed_helper_certificate.py',('--kappa','rel'),
     'canonical_crossed_rel','24f5f424cd27ff9b290ba6ba5a787db08fc556a8f8d6d7718ccc33ef8bfeb1b8'),
    ('canonical_reverse_rel','canonical_crossed_helper_certificate.py',('--kappa','reverse_rel'),
     'canonical_crossed_reverse_rel','fbdbd98627f32da03f5b268944ff7a52cc8b6d40e90a5767508a8ff3687de8b9'),
    ('canonical_affine_a','canonical_crossed_helper_certificate.py',('--kappa','affine_a'),
     'canonical_crossed_affine_a','c302f28963fbe123eaac8b81f940e13213bda9eeacb38e7619a2f5d8b5ada00c'),
    ('canonical_affine_b','canonical_crossed_helper_certificate.py',('--kappa','affine_b'),
     'canonical_crossed_affine_b','b0d41deb172b07eb49d62ae7dcff820eabe5db54b4c234956d42e831211e1e0c'),
)

def sha256(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def reproduce(output):
    source=Path(__file__).resolve().parent
    output=output.resolve()
    if output==source:
        raise ValueError('Choose an output directory different from the input scripts directory.')
    output.mkdir(parents=True,exist_ok=True)
    copied={}
    for name in SCRIPTS:
        src=source/name
        if not src.is_file():raise FileNotFoundError('Missing companion script: '+str(src))
        dest=output/name
        if dest.exists() and dest.is_symlink():
            raise ValueError('Refusing to overwrite an output script symlink: '+str(dest))
        shutil.copyfile(src,dest)
        copied[name]=sha256(dest)
    results=[]
    for mode,script,args,stem,expected in CASES:
        command=[sys.executable,script,*args]
        run=subprocess.run(command,cwd=output,text=True,capture_output=True)
        if run.returncode:
            raise RuntimeError('Certificate mode failed: '+mode+'\n'+run.stdout[-4000:]+run.stderr[-4000:])
        proof_path=output/(stem+'_proofs.json')
        receipt_path=output/(stem+'_receipt.json')
        proof=json.loads(proof_path.read_text())
        receipt=json.loads(receipt_path.read_text())
        actual=sha256(proof_path)
        if receipt.get('status')!='PASS':raise ValueError('Non-PASS receipt: '+mode)
        if actual!=expected or receipt.get('proof_sha256')!=expected:
            raise ValueError('Retained proof hash mismatch: '+mode+'; actual '+actual+'; expected '+expected)
        result={'mode':mode,'status':'PASS','command':[script,*args],
                'proof':proof_path.name,'receipt':receipt_path.name,
                'proof_sha256':actual,'proof_nodes':len(proof['proof_nodes']),
                'formulas':len(proof['formulas']),'roots':len(proof['roots'])}
        results.append(result)
        print('PASS '+mode+': '+str(result['proof_nodes'])+' proof nodes',flush=True)
    aggregate={'status':'PASS','python':sys.version.split()[0],
               'input_scripts_sha256':copied,'modes':results,
               'scope':'Nine finite exploratory proof modes, regenerated from the five copied scripts only; every generated proof hash equals its embedded retained hash. See individual certificates for logical scope. No machine transition-table claim.'}
    receipt_path=output/'research_reproduction_receipt.json'
    receipt_path.write_text(json.dumps(aggregate,indent=2)+'\n')
    print('PASS all '+str(len(results))+' modes; '+str(receipt_path),flush=True)
    return aggregate

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    reproduce(args.output_dir)
if __name__=='__main__':main()
