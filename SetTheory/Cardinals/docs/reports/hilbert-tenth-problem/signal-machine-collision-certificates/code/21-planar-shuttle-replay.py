#!/usr/bin/env python3
"""Verify sealed payload identity, then replay only in fresh external copies."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent
# Filled at release sealing; these pins do not come from the editable checksum list.
PINS = {'README.md': 'c9202b6629735360706cdb8d9164a93af034fbd52a1bca18bb0fe9edfc59046d', 'build.sh': 'fb2db1d5b8bb81bea5835a28c707d2c72d44e09d7624d3b6bf20e4a0a91a07b6', 'figures/make_figures.py': '6d174244a27349a716a0091dbcc3b6eeae747faf013b5d7c2256f82946e24e9f', 'figures/orbits.pdf': 'd3d1104db31cdcc2155c18eaa6a101a65a60e758d099a7d2816de31d0a131f5e', 'figures/rule.pdf': '77b0cd489d89a9522d38cb26268e057de4de79fdc4c854cbfaab5b79142497f3', 'figures/simulation-data.json': 'bdc4296faed980d2c3e431441da27208fa046ee16604cf30bdb6b6db697c4e29', 'report31.pdf': '2528f4ebe04a817fb47dfe5ae1bcf75444b91a5bb1adbb81e5e586a4f8a83957', 'report31.tex': 'e6a38acd7be17efd2785e8b6b99e522e281cebe431b9fb3384cf8f66a85283b6', 'reproduce.sh': 'd8b7ae156d267c31ea9af74a4348149b1566081722d70376205c59cdf351e532', 'scientific/LOCAL_ALGEBRA.md': '6aaad6679b2ba8cd5fd183203a62a054a8b9defdf9a6b29df94cb65ac18acf60', 'scientific/PROOF.md': 'a10c07b450ad16bd1591091c4dc4c0b241ccb00d99fb58f1a77a2e200752a373', 'scientific/audit/assert-hardening-lineage.json': '609635883435263befa2186a9f4cba564d6dd288eb5628e99108b5fc0a45707f', 'scientific/audit/check-results.txt': 'a70397b05b650a0f58afd48b6fb6ea2e97c9dab4f94ea3871dda0aa418ca6cc0', 'scientific/audit/check_essential_inputs.py': '9da256861c6e4870ff1a06cb118e767bffcc5e2416a2d472426f47d835135c99', 'scientific/audit/drift-and-first-arrivals.md': '32b7fe7cde1a48d25fbe88023661af0d071a498e2b6646833550b9b9b2658029', 'scientific/audit/drift-check-results.txt': '273bf96690430d693b0296ce273e0c9d763dbace104c3b7ca3622b7039cb5e9c', 'scientific/audit/essential-input-check-results.txt': 'fdac25092ee7a93f4e755201ef08d057201a28810c87d34df25cf210c854de9b', 'scientific/audit/essential-input-witnesses.json': 'd12d64bb25db17ce9cd9647a3a2d8d1f79bbf1a07865d3e11bef1446e7a9eb98', 'scientific/audit/final-review.md': 'fa03e9a85ea26600148a21ff55e23554ea98570631efd73582e36876600307d3', 'scientific/audit/independent-audit.md': 'f3a4303aff8a9911a604f2b8887c7974e7ef351e8813fa6b3fe6717da49e4cf9', 'scientific/audit/independent_audit.normal.txt': 'a70397b05b650a0f58afd48b6fb6ea2e97c9dab4f94ea3871dda0aa418ca6cc0', 'scientific/audit/independent_audit.optimized.txt': 'a70397b05b650a0f58afd48b6fb6ea2e97c9dab4f94ea3871dda0aa418ca6cc0', 'scientific/audit/independent_audit.py': '59cd532349da67fdfcb2321d1974797f5fa183b8cb19a22fb52351ebb50caa91', 'scientific/audit/independent_drift_audit.normal.txt': '273bf96690430d693b0296ce273e0c9d763dbace104c3b7ca3622b7039cb5e9c', 'scientific/audit/independent_drift_audit.optimized.txt': '273bf96690430d693b0296ce273e0c9d763dbace104c3b7ca3622b7039cb5e9c', 'scientific/audit/independent_drift_audit.py': 'a8b0d9a71216ebd86efd4f64161dc72e8c206b0efaa85ecb2ce997f3f46d4c57', 'scientific/audit/local-quartic-review.md': 'a5ac9090c97d6a0f79e3f6c8f204a765c7325f60b938a8067c350eda58d559af', 'scientific/audit/optimized-audit-validation.json': '842c18e64299b9a039b82056ecbd23fef9dbd3785481d1f9a108284932bec03d', 'scientific/audit/parent-code-review-results.txt': '1921ad859d6f2fb7df974af7b3d7c3636d7b2f9d3341290801182aa5d8e00d24', 'scientific/audit/quartic-reconstruction-normal.txt': '8d4b2608eebce41666f370f29ff5a7cbc299dd99672baaafc05b9ada869ad60c', 'scientific/audit/quartic-reconstruction-optimized.txt': '8d4b2608eebce41666f370f29ff5a7cbc299dd99672baaafc05b9ada869ad60c', 'scientific/audit/quartic-reconstruction-results.json': '8d4b2608eebce41666f370f29ff5a7cbc299dd99672baaafc05b9ada869ad60c', 'scientific/audit/reconstruct_local_quartic.py': '9e5821bd3497303337d8e4953023f3da692029b8ab6a16a568f06d0d64d14dfb', 'scientific/audit/review_parent_code.normal.txt': '1921ad859d6f2fb7df974af7b3d7c3636d7b2f9d3341290801182aa5d8e00d24', 'scientific/audit/review_parent_code.optimized.txt': '1921ad859d6f2fb7df974af7b3d7c3636d7b2f9d3341290801182aa5d8e00d24', 'scientific/audit/review_parent_code.py': 'e557af2a15ea5107d6ce5dbae1595c48ec51bfc09f127c8576f26755c723025a', 'scientific/audit/reviewed-audit-code.sha256': '7d63ad2f0601b73f62d99947c4c7f637ec047b3598e4db55e1b6a112a2433ddb', 'scientific/audit/reviewed-main-files.sha256': 'cbf018c63304526a67895f9e630bb019a91653274c7675f311553eb679ccd8b8', 'scientific/audit/reviewed-supplement-files.sha256': 'a89e66e3096ba9d83c4c98a69050bd1a8fd2d7f74e18612079020d1fa9be850b', 'scientific/audit/upgrade_assert_checks.py': 'd29760b9cf7434e8207da84f254b69cc2d0edc2e8f702e2b4209e8c8f6cb80bb', 'scientific/code/build_local_quartic.py': '05f43fa99773c35838211e68e30ba1c6bd7aaae3f7f93104a778e66918fd0ee0', 'scientific/code/check_local_quartic.py': '90c7061a2e9b743a0b85a74b10b5fd4d86d6401010751c7732894488837b04d2', 'scientific/code/check_shuttle.py': 'f654dc726fa5f892f08be1c3307052f2480a987725c5def8900365fc29b91e80', 'scientific/code/component_rule.py': 'ae0328c1962fa565582befeddb20c0b51faa971d4110e50caaf4d7871699f76a', 'scientific/code/exact_formulas.py': '537f06243b8565c5df47b611319ea1b0d3877fd41df913792d2ab3fe2d2bb1f7', 'scientific/code/local_rule.py': '3e718065a412b1e2c7f238e69a27b5e5198632cbfe623451b60f1e92ae0d78e4', 'scientific/local-quartic-certificate.json': 'e0d9bd288b86e2d3c521a7e40c5945707e61825f992f1741bc5d64be0ae11613', 'scientific/local-rule-certificate.json': '92d4f4265004704c44bbf5d53d1e0d61e29ce1c923d7720a4293b8bb2d2ced8c', 'tamper_regression.py': '445cdd19ce7c118f7f308c040d883314965e290874d901288713a068914e689d', 'verification/expected-cross-implementation.txt': '1921ad859d6f2fb7df974af7b3d7c3636d7b2f9d3341290801182aa5d8e00d24', 'verification/expected-drift.txt': '273bf96690430d693b0296ce273e0c9d763dbace104c3b7ca3622b7039cb5e9c', 'verification/expected-essentiality.txt': 'fdac25092ee7a93f4e755201ef08d057201a28810c87d34df25cf210c854de9b', 'verification/expected-independent.txt': 'a70397b05b650a0f58afd48b6fb6ea2e97c9dab4f94ea3871dda0aa418ca6cc0', 'verification/expected-local-rule.json': '92d4f4265004704c44bbf5d53d1e0d61e29ce1c923d7720a4293b8bb2d2ced8c', 'verification/expected-primary.json': 'f4ceba6a8d2637ede7ad0546f024508a6a9d4a7a2f0d7b897cdfa1bb121467ba', 'verification/expected-quartic-checks.json': '59ca8a1e24a87c99354637fb9d291f89578322751ace0c1f293d613fb640b07c', 'verification/expected-quartic-counts.json': 'd4cf053e5fe09ac952717f99186d16642d587705655eb93a2484c05031e7daee', 'verification/expected-quartic-reconstruction.json': '8d4b2608eebce41666f370f29ff5a7cbc299dd99672baaafc05b9ada869ad60c', 'verification/expected-replay-summary.json': '4bbeabe2357c12b1d82b763baf17a27a733bce667f80566b3a27c5f891670b3f', 'verification/source-lineage.json': '6f40936ab7461ec0c7e9745ceea839841566a0457a8b29b746f66a244f0a293f'}
BOOTSTRAP_FILES={'replay.py','SHA256SUMS'}

def require(condition,message):
    if not condition: raise RuntimeError(message)

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def verify_identity():
    require(bool(PINS),'Payload has not been sealed')
    actual=set()
    for p in ROOT.rglob('*'):
        require(not p.is_symlink(),'Symlink is not permitted: '+str(p.relative_to(ROOT)))
        if p.is_file(): actual.add(p.relative_to(ROOT).as_posix())
    require(actual==set(PINS)|BOOTSTRAP_FILES,'Required payload file set mismatch')
    for name,wanted in PINS.items():
        require(digest(ROOT/name)==wanted,'Pinned payload digest mismatch: '+name)

def snapshot():
    result={}
    for p in sorted(ROOT.rglob('*')):
        st=p.stat(); name=p.relative_to(ROOT).as_posix()
        result[name]=(digest(p) if p.is_file() else None,stat.S_IMODE(st.st_mode),st.st_mtime_ns)
    return result

def typed_equal(a,b,label='receipt'):
    require(type(a) is type(b),label+': exact type mismatch')
    if type(b) is dict:
        require(set(a)==set(b),label+': key mismatch')
        for k in b: typed_equal(a[k],b[k],label+'.'+k)
    elif type(b) is list:
        require(len(a)==len(b),label+': length mismatch')
        for i,(x,y) in enumerate(zip(a,b)):typed_equal(x,y,label+'['+str(i)+']')
    else: require(a==b,label+': value mismatch')

def types_regression():
    pairs=[(True,1),(1,True),(1.0,1),({'n':True},{'n':1}),([False],[0])]
    for a,b in pairs:
        try:typed_equal(a,b)
        except RuntimeError:pass
        else:raise RuntimeError('Typed comparison accepted different JSON types')
    typed_equal({'ok':True,'n':1,'x':[0,'a',None]},{'ok':True,'n':1,'x':[0,'a',None]})
    return {'status':'PASS','different_type_pairs_rejected':len(pairs)}

def read_json(path):
    def no_duplicates(items):
        result={}
        for k,v in items:
            require(k not in result,'Duplicate JSON key: '+k);result[k]=v
        return result
    return json.loads(path.read_text(),object_pairs_hook=no_duplicates)

# -I excludes ambient PYTHONPATH and user-site packages. Only the selected copied
# script directory is inserted so the approved sibling imports remain available.
LAUNCH='import runpy,sys; sys.path.insert(0,sys.argv[1]); p=sys.argv[2]; sys.argv=sys.argv[2:]; runpy.run_path(p,run_name="__main__")'

def run_script(work,relative,flags,args=()):
    script=work/'scientific'/relative
    done=subprocess.run([sys.executable,'-I','-B',*flags,'-c',LAUNCH,str(script.parent),str(script),*map(str,args)],cwd=work/'scientific',capture_output=True,text=True,timeout=900)
    require(done.returncode==0,relative+' failed: '+done.stderr[-4000:])
    return done.stdout

def replay(output):
    out=output.resolve()
    require(out!=ROOT and ROOT not in out.parents,'Output directory must be external to release')
    require(not out.exists() or (out.is_dir() and not any(out.iterdir())),'Output directory must be absent or empty')
    out.mkdir(parents=True,exist_ok=True)
    before=snapshot(); all_records={}
    expected={label:read_json(ROOT/'verification'/('expected-'+label+'.json')) for label in ['primary','local-rule','quartic-checks','quartic-counts','quartic-reconstruction']}
    require(expected['primary']['status']=='PASS' and expected['quartic-checks']['status']=='PASS','Expected receipts must be passing')
    for mode,flags in [('normal',[]),('optimized',['-O'])]:
        with tempfile.TemporaryDirectory(prefix='report31-'+mode+'-') as tmp:
            work=Path(tmp);shutil.copytree(ROOT/'scientific',work/'scientific',copy_function=shutil.copy2)
            rec={}
            stdout=run_script(work,'code/check_shuttle.py',flags,['--output',work/'primary.json','--certificate',work/'local-rule.json'])
            for label in ['primary','local-rule']:
                rec[label]=read_json(work/(label+'.json'));typed_equal(rec[label],expected[label],label+' '+mode)
            (out/('primary-'+mode+'.log')).write_text(stdout)
            stdout=run_script(work,'code/build_local_quartic.py',flags,['--output',work/'quartic.json'])
            rec['quartic-counts']=json.loads(stdout);typed_equal(rec['quartic-counts'],expected['quartic-counts'],'quartic counts '+mode)
            require((work/'quartic.json').read_bytes()==(ROOT/'scientific/local-quartic-certificate.json').read_bytes(),'Generated quartic bytes mismatch')
            stdout=run_script(work,'code/check_local_quartic.py',flags,['--certificate',work/'quartic.json','--output',work/'quartic-checks.json'])
            rec['quartic-checks']=read_json(work/'quartic-checks.json');typed_equal(rec['quartic-checks'],expected['quartic-checks'],'quartic checks '+mode)
            for label,script in [('independent','independent_audit.py'),('drift','independent_drift_audit.py'),('cross-implementation','review_parent_code.py'),('essentiality','check_essential_inputs.py')]:
                stdout=run_script(work,'audit/'+script,flags)
                require(stdout==(ROOT/'verification'/('expected-'+label+'.txt')).read_text(),label+' receipt differs')
                rec[label]=stdout;(out/(label+'-'+mode+'.txt')).write_text(stdout)
            stdout=run_script(work,'audit/reconstruct_local_quartic.py',flags)
            rec['quartic-reconstruction']=read_json(work/'scientific/audit/quartic-reconstruction-results.json')
            typed_equal(rec['quartic-reconstruction'],expected['quartic-reconstruction'],'geometric reconstruction '+mode)
            (out/('quartic-reconstruction-'+mode+'.log')).write_text(stdout)
            (out/('receipts-'+mode+'.json')).write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
            all_records[mode]=rec
    typed_equal(all_records['normal'],all_records['optimized'],'normal versus optimized')
    types=types_regression()
    require(snapshot()==before,'Release bytes, modes or mtimes changed')
    summary={'status':'PASS','normal_optimized_exact_typed_equality':True,'payload_bytes_modes_mtimes_preserved':True,'identity_verified_before_scientific_execution':True,'json_type_regression':types,'checks':['primary','local-rule','quartic-counts','quartic-checks','independent','drift','cross-implementation','essentiality','quartic-reconstruction'],'scope':'Finite replay of this pinned artifact; global and unique-witness results are proved in the report'}
    typed_equal(summary,read_json(ROOT/'verification/expected-replay-summary.json'),'final replay summary')
    (out/'replay-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps(summary,indent=2,sort_keys=True))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    group=p.add_mutually_exclusive_group(required=True);group.add_argument('--verify-only',action='store_true');group.add_argument('--self-test-types',action='store_true');group.add_argument('--output-dir',type=Path)
    args=p.parse_args();verify_identity()
    if args.verify_only:print('PASS: exact required payload set and embedded SHA-256 pins verified; no scientific code executed')
    elif args.self_test_types:print(json.dumps(types_regression(),sort_keys=True))
    else:replay(args.output_dir)
if __name__=='__main__':main()
