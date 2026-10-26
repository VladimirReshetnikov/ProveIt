#!/usr/bin/env python3
"""Verify the complete release using exact finite certificates.

No finite check substitutes for the unbounded mathematical theorem.
Use --with-source for a fresh full replay of the retained arithmetic ancestry.
"""
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def need(c,m):
    if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(rel,args=()):
    cmd=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(ROOT/rel)]+list(map(str,args))
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    if sys.flags.optimize:env['PYTHONOPTIMIZE']='1'
    p=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True)
    need(p.returncode==0,rel+' failed:\n'+p.stdout+'\n'+p.stderr)
    return p.stdout
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--with-source',action='store_true');ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    result={'status':'PASS','optimized':bool(sys.flags.optimize)}
    manifest=ROOT/'MANIFEST.sha256.json'
    if manifest.exists():
        items=json.loads(manifest.read_text())['files']
        for name,digest in items.items():need(sha(ROOT/name)==digest,'Manifest '+name)
        result['manifest_files']=len(items)
    ledger=json.loads((ROOT/'inherited/source172_PROVENANCE.json').read_text())
    for entry in ledger['files']:
        p=ROOT/'inherited'/entry['retained_path']
        need(p.is_file() and sha(p)==entry['sha256'],'Inherited source provenance '+entry['retained_path'])
    need((ROOT/'inputs/source216.json').read_bytes()==(ROOT/'inherited/source172_signed/stages/affine216/equation.json').read_bytes(),'Actual parent chart binding')
    result['authenticated_inherited_files']=len(ledger['files'])
    result['theorem_regressions']=json.loads(run('check_theorem.py'))
    result['source_interface']=json.loads(run('code/audit_source_interface.py'))
    result['raw_fusion']=json.loads(run('verify_independent.py'))
    result['matched_control']=json.loads(run('code/check_matched_control.py'))
    result['printed_equations']=json.loads(run('code/check_report.py'))
    with tempfile.TemporaryDirectory(prefix='conzfc_mixed_verify_') as td:
        tmp=Path(td);pr=tmp/'projections.json'
        run('code/audit_projections.py',['--output',pr]);result['projections']=json.loads(pr.read_text())
        dest=tmp/'equations';run('build.py',['--output',dest])
        for p in sorted((ROOT/'inputs').glob('monic_profile_integer*.json')):run('compile_projection.py',[p,'--output',dest])
        generated=list(dest.rglob('*.json'))
        for p in generated:need(p.read_bytes()==(ROOT/'equations'/p.relative_to(dest)).read_bytes(),'Deterministic rebuild '+str(p.relative_to(dest)))
        result['byte_exact_rebuilt_files']=len(generated)
    heights={}
    for p in sorted((ROOT/'equations').glob('*/circuit.json')):
        c=json.loads(p.read_text());met=json.loads((p.parent/'METRICS.json').read_text());bounds=[]
        for n in c['nodes']:
            if n[0]=='var':v=1
            elif n[0]=='const':v=abs(n[1])
            elif n[0]=='*':v=bounds[n[1]]*bounds[n[2]]
            else:v=bounds[n[1]]+bounds[n[2]]
            bounds.append(v)
        bits=bounds[c['output']].bit_length()
        need(bits==met['coefficient_height_strictly_less_than_2_power'],'Coefficient height bound')
        heights[p.parent.name]=bits
    result['expanded_height_upper_bound_bits']=heights
    if args.with_source:result['source_replay']=json.loads(run('inherited/source172_signed/verify.py',['--rebuild']))
    result['scope']='Exact finite artifacts, witness maps, degree/liveness and arithmetic samples. Unbounded pooling proof and inherited ZFC calibration are separate ordinary proofs.'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS','optimized':result['optimized'],'rebuilt_files':result['byte_exact_rebuilt_files'],'inherited_files':len(ledger['files']),'projection_endpoints':len(result['projections']['endpoints']),'source_replayed':args.with_source},sort_keys=True))
if __name__=='__main__':main()
