#!/usr/bin/env python3
"""Run the complete finite verification chain offline (Python standard library)."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import zipfile

ROOT=Path(__file__).resolve().parent
PARENT='ConZFC_Pooled_Projection_2026-10-25'
PARENT_SHA='a91308bd0c82182ea15080763cb23cb4fa0aa45a812eabb7a6cbcd21c0b95a06'
def require(condition,message):
    if not condition:raise ValueError(message)
def read(path):
    return json.loads(Path(path).read_text())
def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def run_json(*args):
    command=[sys.executable,'-B']
    if sys.flags.optimize:command.append('-O')
    proc=subprocess.run(command+[str(a) for a in args],cwd=ROOT,
                        capture_output=True,text=True)
    if proc.returncode:
        raise RuntimeError('Failed: '+str(args[0])+'\n'+proc.stdout+proc.stderr)
    return json.loads(proc.stdout)
def equal_files(a,b,label):
    require(Path(a).read_bytes()==Path(b).read_bytes(),label)
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path,help='Write the complete JSON result here')
    parser.add_argument('--rebuild',action='store_true',
                        help='Also reconstruct all seed and reduced equation files byte for byte')
    args=parser.parse_args()
    provenance=read(ROOT/'provenance/SOURCES.json')
    for item in provenance['retained_files']:
        require(digest(ROOT/item['local_path'])==item['sha256'],
                'retained-source digest: '+item['local_path'])
    require(digest(ROOT/'source/equation216.json')==PARENT_SHA,'literal P216 identity')
    result={'status':'PASS','python_optimized':bool(sys.flags.optimize),
            'comparison_commit':provenance['comparison_commit']}
    with tempfile.TemporaryDirectory(prefix='conzfc-parent-') as temporary:
        temporary=Path(temporary)
        with zipfile.ZipFile(ROOT/'source'/f'{PARENT}.zip') as archive:
            for member in archive.infolist():
                destination=(temporary/member.filename).resolve()
                require(destination.is_relative_to(temporary.resolve()),'safe archive path')
            archive.extractall(temporary)
        parent=temporary/PARENT
        equal_files(parent/'algebra/equation216.json',ROOT/'source/equation216.json',
                    'parent-to-seed byte-exact boundary')
        result['parent_replay']=run_json(parent/'verify.py')
        require(result['parent_replay']['final_equation_sha256']['216']==PARENT_SHA,
                'parent replay authenticated intended equation')
        ports_path=temporary/'ports.json'
        run_json(ROOT/'code/audit_parent_ports.py','--parent',parent,'--output',ports_path)
        ports=read(ports_path)
        require(ports==read(ROOT/'verification/P216_PORTS_AUDIT.json'),
                'independent port audit agrees exactly with supplied source binding')
        result['parent_ports']={'status':'PASS','requests':len(ports['requests']),
            'frame_atoms':len(ports['frame_atoms']),
            'raw_anchor_identities':len(ports['raw_anchor_before_orientation']),
            'sha256':digest(ports_path)}
        result['p207']=run_json(ROOT/'code/verify_p207.py','--ports',ports_path)
        result['seed_family']=run_json(ROOT/'code/verify_family.py','--ports',ports_path)
    copies=[
        ('source216.json','source/equation216.json'),
        ('source207.json','equations/P207.json'),
        ('source206_joint.json','equations/P206_joint.json'),
        ('source209.json','equations/partitions/P209.json'),
        ('source211.json','equations/partitions/P211.json'),
        ('source208_joint.json','equations/partitions/P208_joint.json'),
        ('source210_joint.json','equations/partitions/P210_joint.json')]
    for local,source in copies:
        equal_files(ROOT/'higher_degree'/local,ROOT/source,'elimination source boundary '+local)
    result['elimination_source_boundaries']={'status':'PASS','byte_exact_files':len(copies)}
    result['reduced_family']=run_json(ROOT/'higher_degree/verify.py')
    metrics=read(ROOT/'higher_degree/RESULTS.json')
    for record in metrics:
        document=read(ROOT/'higher_degree/equations'/record['file'])
        for key,value in record.items():
            if key in ('file','base_file'):continue
            require(document['metrics'][key]==value,'published metric: '+record['file']+' '+key)
        require(document['base_file']==record['base_file'],'published seed')
    result['published_results']={'status':'PASS','profiles':len(metrics)}
    result['printed_formulas']=run_json(ROOT/'code/check_report.py')
    result['oriented_arithmetic_fixtures']=run_json(ROOT/'code/check_arithmetic.py')
    result['joint_arithmetic_fixtures']=run_json(ROOT/'code/check_joint_arithmetic.py')
    if args.rebuild:
        result['seed_rebuild']=run_json(ROOT/'code/check_rebuild.py')
        result['reduced_rebuild']=run_json(ROOT/'higher_degree/build.py','--check')
    result['proof_boundary']=(
        'Exact finite source, polynomial, port, row, substitution, degree, dependence, '
        'and printed-formula checks. Unbounded arithmetic soundness/completeness and the '
        'named C222/ZF/ZFC logical calibration are ordinary mathematical dependencies. '
        'No proof of consistency and no new end-to-end proof-assistant build.')
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(encoded)
    print(encoded,end='')
if __name__=='__main__':main()

