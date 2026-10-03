#!/usr/bin/env python3
"""Replay checks in isolated temporary storage; never overwrite the release."""
import argparse,hashlib,json,pathlib,shutil,subprocess,sys,tempfile
P=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--full',action='store_true');ap.add_argument('--build',action='store_true');args=ap.parse_args()
manifest=P/'SHA256SUMS'
if not manifest.is_file():
    raise SystemExit('FAIL missing SHA256SUMS; use the complete release package')
seen=set()
for line in manifest.read_text().splitlines():
    sha,name=line.split('  ',1)
    path=pathlib.PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or name in seen:
        raise SystemExit('FAIL invalid or duplicate manifest path: '+name)
    seen.add(name)
    if hashlib.sha256((P/name).read_bytes()).hexdigest()!=sha:
        raise SystemExit('FAIL release hash: '+name)
required={'README.md','a113226-refined-addendum.pdf','a113226-refined-addendum.tex',
          'refined-proof.md','mathematical-review.md','typesetting-review.md','reproduction-review.md',
          'literature-screen.md','refined_coefficients.py','refined_coefficients.json',
          'root_two_saddle_audit.py','root_two_saddle_audit.json',
          'independent_b3_audit.py','independent_b3_audit.json',
          'fresh-independent-audit.py','fresh-independent-audit.json','root-refinement-review.md',
          'verify_record_bijection.py','record_bijection_validation.json',
          'validate_refinement.py','validation.json','exact_rows.json',
          'verify_package.py','verify.sh','build.sh','requirements.txt'}
if not required.issubset(seen):
    raise SystemExit('FAIL incomplete manifest: '+', '.join(sorted(required-seen)))
print('PASS release hashes ('+str(len(seen))+' files)',flush=True)
with tempfile.TemporaryDirectory(prefix='a113226-refined-replay-') as tmp:
    Q=pathlib.Path(tmp)
    for name in ['refined_coefficients.py','validate_refinement.py','verify_record_bijection.py','root_two_saddle_audit.py','independent_b3_audit.py','fresh-independent-audit.py',
                 'exact_rows.json','refined-proof.md','a113226-refined-addendum.tex']:
        shutil.copy2(P/name,Q/name)
    def run(*cmd):subprocess.run(cmd,cwd=Q,check=True,stdout=subprocess.DEVNULL)
    run(sys.executable,'refined_coefficients.py','--order','3')
    assert json.loads((Q/'refined_coefficients.json').read_text())==json.loads((P/'refined_coefficients.json').read_text())
    audit=subprocess.check_output([sys.executable,'root_two_saddle_audit.py'],cwd=Q,text=True)
    assert json.loads(audit)==json.loads((P/'root_two_saddle_audit.json').read_text())
    audit3=subprocess.check_output([sys.executable,'independent_b3_audit.py'],cwd=Q,text=True)
    assert json.loads(audit3)==json.loads((P/'independent_b3_audit.json').read_text())
    run(sys.executable,'fresh-independent-audit.py')
    assert json.loads((Q/'fresh-independent-audit.json').read_text())==json.loads((P/'fresh-independent-audit.json').read_text())
    run(sys.executable,'verify_record_bijection.py','--n','8')
    assert json.loads((Q/'record_bijection_validation.json').read_text())==json.loads((P/'record_bijection_validation.json').read_text())
    print('PASS saddle algorithms, independent symbolic/direct-poset audits, and bijection checks',flush=True)
    N=400 if args.full else 120
    run(sys.executable,'validate_refinement.py','--n',str(N),'--brute','8')
    actual=json.loads((Q/'exact_rows.json').read_text());expected=json.loads((P/'exact_rows.json').read_text())
    assert actual==expected[:N+1]
    result=json.loads((Q/'validation.json').read_text());reference=json.loads((P/'validation.json').read_text())
    assert result.keys()==reference.keys()
    assert result['N']==N
    for key,entries in result.items():
        if key in ('N','elapsed_seconds'):continue
        expected_entries=reference[key]
        if key!='initial_rows':
            expected_entries=[entry for entry in expected_entries if entry.get('n',0)<=N]
        assert entries==expected_entries,key
    print('PASS exact rows through',N,'and recorded numerical samples',flush=True)
    if args.build:
        for name in ['a113226-refined-addendum.tex','build.sh']:shutil.copy2(P/name,Q/name)
        run('bash','build.sh')
        assert (Q/'a113226-refined-addendum.pdf').read_bytes()==(P/'a113226-refined-addendum.pdf').read_bytes()
        print('PASS byte-identical PDF rebuild',flush=True)
print('PASS all requested release checks')
