#!/usr/bin/env python3
"""Proposed batch163 replay. NOT RUN by the intake reviewer.

Copies one pristine extracted package into a NEW external output directory.
Executes only reviewed Python witness/certificate checks, serially, with a
120-second cap per command. No manifests, search generators, C++, Z3, Lean,
version queries, dependency installation, or repository writes.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',required=True,type=int,choices=(64,65))
    ap.add_argument('--package',required=True,type=Path)
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--replay-ledger',action='store_true',help='Source65 only: replay all130872 saved failure witnesses, not a new search.')
    a=ap.parse_args();assert __debug__
    assert not a.output.exists(),'Choose a new output directory'
    if a.replay_ledger:assert a.source==65
    a.output=a.output.resolve();a.output.mkdir(parents=True)
    p=a.output/'package';shutil.copytree(a.package.resolve(),p)
    env=os.environ.copy();env.pop('ZFC246_TABLE',None);env['PYTHONDONTWRITEBYTECODE']='1'
    jobs=[];adapters=[]
    def job(label,args,cwd=p):jobs.append((label,[sys.executable,'-B',*map(str,args)],cwd))
    if a.source==64:
        base=p/'baseline/context246';env['ZFC246_BASE']=str(base)
        job('fresh baseline macro dependencies',['code/check_macro_inductions.py'],base)
        job('245 decrement and INC counterexample',['experiments/tail/verify_decrement245.py','--base',base,'--output-dir',p/'experiments/tail'])
        job('244 forward carry induction',['experiments/forward/prove_forward_carry.py'])
        job('244 full-configuration collisions',['experiments/forward/check_collision.py'])
        job('48 return-premise counterexample',['experiments/runtime/verify_return_counterexample.py'])
        job('all8391 detector-entry contracts',['experiments/tail/audit_detector_entry.py','--base',base,'--output',p/'experiments/tail/detector-entry-audit.json'])
        for model in ['detector_n8_t8_wNone_fix0_nowrite0_seed0_left-7_exit-8_head-8.json','result_n8_t8_wNone.json']:
            job('SAT detector literal replay '+model,['experiments/decoder/verify_detector.py',p/'experiments/counter'/model])
        job('alternate42-row induction support',['experiments/decoder/audit_detector_support.py'])
        job('alternate8391 and whole-tape bootstrap',['experiments/decoder/verify_alternate.py'])
    else:
        base=p/'baseline246/zfc-context246'
        job('fresh baseline macro dependencies',['code/check_macro_inductions.py'],base)
        extra=['--replay-ledger'] if a.replay_ledger else []
        job('8391 support, saved domains and SAT positive control',['code/check_saved_results.py',*extra,'--output',a.output/'saved-results.json'])
        job('prepared source-phase and scanner witnesses',['audit/verify_audit.py','--output',a.output/'audit'])
        # The delivered context wrapper embeds a checksum-manifest pass. Keep
        # it unchanged; a separate sibling adapter preserves all preceding
        # mathematical checks and changes the status text to state the omission.
        original=p/'context/check_support.py';text=original.read_text()
        before="    manifest=f.ROOT/'SUPPORT_SHA256SUMS'\n"
        start=text.index(before);end=text.index("\nif __name__=='__main__':main()",start)
        removed=text[start:end]
        assert removed=="    manifest=f.ROOT/'SUPPORT_SHA256SUMS'\n    if manifest.exists():\n        for line in manifest.read_text().splitlines():\n            digest,path=line.split('  ',1)\n            assert sha256((f.ROOT/path).read_bytes()).hexdigest()==digest,path\n    print('SUPPORT CHECKS PASS: baseline8391, literal false-sentinel witnesses, exact family counts, and delivered-byte manifest.')\n"
        adapter=p/'context/review_check_support_no_manifests.py'
        adapter.write_text(text[:start]+"    print('SUPPORT CHECKS PASS: baseline8391, literal false-sentinel witnesses, exact family counts; checksum manifests deliberately omitted.')\n"+text[end:])
        adapters.append(dict(original=str(original),original_sha256=sha(original),adapter=str(adapter),adapter_sha256=sha(adapter),change='Only checksum-manifest loop and corresponding status wording omitted; delivered source unchanged.'))
        job('context derived macros and saved counts',[adapter],p/'context')
        job('product and relational inductive closure',['alternative/verify_invariant.py','--relational'])
    records=[];out=dict(status='RUNNING',source=a.source,source_package=str(a.package.resolve()),working_package=str(p),checksum_manifests_checked=False,line_endings_checked=False,compiler_invoked=False,new_search_run=False,one_incoming_journal_replayed=a.replay_ledger,reference_full_suite_replayed=False,adapters=adapters,commands=records)
    for i,(label,cmd,cwd) in enumerate(jobs,1):
        print(f'[{i}/{len(jobs)}] {label}',flush=True);began=time.monotonic()
        try:
            r=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True,timeout=120)
            stdout,stderr,rc=r.stdout,r.stderr,r.returncode
        except subprocess.TimeoutExpired as e:
            stdout=e.stdout or '';stderr=e.stderr or ''
            if isinstance(stdout,bytes):stdout=stdout.decode(errors='replace')
            if isinstance(stderr,bytes):stderr=stderr.decode(errors='replace')
            rc=124
        op=a.output/f'{i:02d}.stdout.txt';ep=a.output/f'{i:02d}.stderr.txt';op.write_text(stdout);ep.write_text(stderr)
        records.append(dict(label=label,command=cmd,cwd=str(cwd),returncode=rc,seconds=time.monotonic()-began,stdout=str(op),stderr=str(ep),stdout_sha256=sha(op),stderr_sha256=sha(ep)))
        out['status']='FAIL' if rc else 'RUNNING';(a.output/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
        if rc:raise SystemExit(rc)
    if a.source==64:
        x=json.loads((p/'experiments/forward/collision.json').read_text());assert len(x['examples'])==3
        assert [len(v['zero_trace'])-1 for v in x['examples']]==[14,46,48]
    else:
        x=json.loads((p/'alternative/results/invariant-verification.json').read_text());assert x['relational']['checked_abstract_edges']==8669994
    out['status']='PASS';out['scope']='Fresh reviewed certificate/witness jobs only. Preserved search summaries are scoped records, not replayed searches or lower-bound proofs. No Lean/Rocq endpoint.'
    (a.output/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(records),'reviewed jobs',flush=True)
if __name__=='__main__':main()
