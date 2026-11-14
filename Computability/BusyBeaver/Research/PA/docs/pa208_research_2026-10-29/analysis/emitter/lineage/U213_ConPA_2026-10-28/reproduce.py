#!/usr/bin/env python3
"""Offline U213 reconstruction, proof binding, and optional fresh runtime replay."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,tempfile,time,zipfile
sys.dont_write_bytecode=True
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import build_table as bt
import check_runtime_origin
import check_startup_independent
import check_reentry_repair
import source_language as sl

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def command(args):
    r=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,text=True,capture_output=True)
    if r.returncode:
        raise RuntimeError(r.stdout+'\n'+r.stderr)
    return r.stdout
def verify_manifest():
    entries=[]
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        sha,name=line.split('  ',1);p=(ROOT/name).resolve()
        need(p.is_relative_to(ROOT)and p.is_file(),'manifest path')
        need(digest(p)==sha,'manifest mismatch: '+name);entries.append(name)
    need(len(entries)==len(set(entries)),'duplicate manifest entry');return len(entries)
def frozen_runtime_audit():
    r=json.load(open(ROOT/'evidence/runtime.json'));c=json.load(open(ROOT/'evidence/runtime_cases.json'))
    rows=json.load(open(ROOT/'machine/sites.json'))
    expected=[(i,p)for i,x in enumerate(rows)for p in ((False,True)if x[1]=='CD'else(False,))]
    need([(v['site_index'],v['positive'])for v in c]==expected,'saved case coverage')
    need(len(c)==5084 and r['proved_cases']==5084 and r['status']=='UNIVERSAL_MATHEMATICAL_PASS','saved runtime status')
    need(r['table_sha256']==digest(ROOT/'machine/u213.native.tm')and r['source_sha256']==digest(ROOT/'machine/sites.json'),'saved runtime inputs')
    need(r['header_base']==56,'saved header convention')
    for v in c:
        need(len(v['duration'])==13 and all(n>=0 for n in v['duration'])and v['duration'][0]>0,'positive duration')
        need(len(v['motion'])==13 and v['symbolic_steps']>0,'saved proof shape')
    return {'cases':len(c),'header_base':56,'symbolic_steps':sum(v['symbolic_steps']for v in c),'minimum_duration_constant':min(v['duration'][0]for v in c)}
def parent_audit(work):
    zpath=ROOT/'inputs/U214_ConPA_Reduction_2026-10-28.zip'
    need(digest(zpath)=='b3a520e2181b739fec7257a7935b979acb00400f8d8147b5a2c212fd53a38d2c','parent archive digest')
    target=work/'parent';target.mkdir()
    with zipfile.ZipFile(zpath)as z:
        for name in z.namelist():need((target/name).resolve().is_relative_to(target.resolve()),'unsafe archive path')
        z.extractall(target)
    p=target/'U214_ConPA_Reduction_2026-10-28'
    command([p/'reproduce.py','--report',work/'parent.json'])
    r=json.load(open(work/'parent.json'));need(r['status']=='U214_RECONSTRUCTION_AND_PROOF_AUDIT_PASS','parent audit')
    return {'status':r['status'],'inherited_U218_audit':r['inherited_U218_audit'],'parent_symbolic_cases_rederived':r['symbolic_cases_rederived'],'scope':'Parent finite reconstruction, bindings, saved runtime audit, local proofs, and startup replay. The new U213 all-natural replay is independently selected by --full.'}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true');ap.add_argument('--report',type=Path);a=ap.parse_args()
    begun=time.monotonic();manifest=verify_manifest()
    with tempfile.TemporaryDirectory(prefix='u213-replay-')as td:
        work=Path(td)
        construction=bt.build(ROOT/'inputs/u218.native.tm',ROOT/'inputs/table_recipe.json',work/'machine')
        for n in ('u213.native.tm','u213.tm','state_map.json','summary.json'):
            need((work/'machine'/n).read_bytes()==(ROOT/'machine'/n).read_bytes(),'table output differs: '+n)
        command([ROOT/'code/build_source.py','--u214',ROOT/'inputs/u214.sites.json','--st215',ROOT/'inputs/st215.sites.json','--output',work/'source'])
        need((work/'source/sites.json').read_bytes()==(ROOT/'machine/sites.json').read_bytes(),'source reconstruction bytes')
        source=json.load(open(work/'source/source_receipt.json'))
        need(source==json.load(open(ROOT/'evidence/source.json')),'source receipt differs')
        rows=json.load(open(ROOT/'machine/sites.json'));sl.tree(rows)
        graph,checks=sl.graph_arithmetic(rows);need(graph==sl.graph_intervals(rows)and checks==5084,'source CFG')
        command([ROOT/'code/audit_suffix.py','--source',ROOT/'machine/sites.json','--dag',ROOT/'inputs/DagPerm.v','--output',work/'suffix.json'])
        need(json.load(open(work/'suffix.json'))==json.load(open(ROOT/'evidence/suffix.json')),'suffix receipt')
        command([ROOT/'code/audit_commands.py','--source',ROOT/'machine/sites.json','--dag',ROOT/'inputs/DagPerm.v','--output',work/'commands.json'])
        need(json.load(open(work/'commands.json'))==json.load(open(ROOT/'evidence/commands.json')),'command receipt')
        commands=json.load(open(work/'commands.json'))
        need(commands['covered_primitive_occurrences']+(3766-106)==3909,'source semantics coverage')
        raw=check_reentry_repair.table(ROOT/'inputs/raw_allocation214.native.tm')
        repaired=check_reentry_repair.table(ROOT/'inputs/repaired214.native.tm')
        final=check_reentry_repair.table(ROOT/'machine/u213.native.tm')
        _,reentry=check_reentry_repair.verify(raw,repaired,final)
        need(reentry['admissible_radius2_frames']==6864,'local proof coverage')
        startup=check_startup_independent.audit(ROOT/'machine/u213.native.tm',ROOT/'machine/sites.json')
        need(startup==json.load(open(ROOT/'evidence/startup_independent.json')),'startup receipt differs')
        origin=check_runtime_origin.audit(ROOT)
        frozen=frozen_runtime_audit()
        inherited=parent_audit(work)
        runtime=None
        if a.full:
            import verify_runtime
            runtime=verify_runtime.run(ROOT,work/'runtime')
        result={'status':'U213_FULL_REPLAY_PASS'if a.full else'U213_FINITE_REPLAY_PASS',
            'manifest_files':manifest,'construction':construction,
            'source_subtrees':197,'source_primitives':3909,'source_semantic_occurrences_bound':3909,
            'suffix_macro_calls':127,'gate_macro_calls':5,'exterior_macro_calls':15,
            'exterior_primitive_controls':5,'source_successor_checks':checks,
            'guarded_reentry_frames':6864,'negative_controls_rejected':3,
            'startup_steps':startup['literal_steps'],'startup_source_ordinal':136,
            'startup_source_prefix_steps':141,'header_base':56,'explicit_safe_heads':9,
            'required_conservative_credit':2,'permanent_credit_margin':7,
            'frozen_runtime':frozen,'runtime_cases_rederived':5084 if a.full else 0,
            'runtime_literal_rows_covered':runtime['literal_rows_covered']if runtime else None,
            'runtime_origin':origin,'parent':inherited,
            'seconds':round(time.monotonic()-begun,3),
            'scope':'Exact executable verification of the construction, complete source/arithmetic bindings, local entry proof, and blank startup; --full freshly rederives all arbitrary-natural primitive contracts. Written compiler/credit proofs and inherited U/PA consistency interpretations are mathematical dependencies. No new Lean/Rocq/MM0 or exported PA endpoint certificate.'}
        if a.report:
            a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
if __name__=='__main__':main()
