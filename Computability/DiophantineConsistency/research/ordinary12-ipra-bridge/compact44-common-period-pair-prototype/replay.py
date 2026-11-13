#!/usr/bin/env python3
"""Prelaunch draft: 24-child same-side common-period pair."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S -B, without optimization')
HERE=Path(__file__).resolve().parent
BASE=HERE.parent
ROOT=HERE.parents[2]
REPOSITORY=ROOT.parents[1]
PLAN=BASE/'compact44-common-period-closure-plan'
PARENT_AUDIT=ROOT/'reviews/compact44-direct-symbolic-k-pair-independent-audit'
CLOSURE_AUDIT=ROOT/'reviews/compact44-common-period-closure-independent-audit'
PREFIX=Path('/tmp/ipra-direct-symbolic-k-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.py':'c24776e989d37ec42a3e7f7236c4d768a2d10dedcd9f82c2f1d24c222cf9c4cc',PLAN/'scan.json':'a14687e94930f3b180a01e689ef1ee8ccf29abb0de95e30fef9b4396b1076a1a',PLAN/'README.md':'aa458aafc8a27d3d22d33d2a2bc5430aec3e85ef21be28b3444744e6b4dd03c9',PLAN/'terminal-observation.json':'f5a295f74604dd19c1ad9dbf646f12454bb4ca092af68f8912196a59aec8b664',
 CLOSURE_AUDIT/'audit.py':'c5a54227061838872251d96157a54a6a6a6123e68af6d1a78972b5a3cdf6fbee',CLOSURE_AUDIT/'CHECK.json':'e2f659efcd13b2ba484c2f4d4700d57a718f1c86dc9eef2bfa556c36a028f81c',CLOSURE_AUDIT/'terminal-observation.json':'ddfbf73b31bfadde24490b11b341d5e96ace8d5273cdfa3625f223540fa46c5b',
 PARENT_AUDIT/'audit.py':'4e8bdbe5217c8b19bda4e573d6fa5f7d069cd26f700127402639925ca5be9093',PARENT_AUDIT/'CHECK.json':'5aecb3c05962fd5f13650899bac9ce6f2406827a8d08f43714ddd2966716a634',PARENT_AUDIT/'terminal-observation.json':'51feb6dba903581ab36824efa3c816a4b4e6c2d8b44d63030e0971acf82f73a3'}
MODULES=['DiophantineConsistency.FreeJGraphCongruenceExplore', 'DiophantineConsistency.CompactSymbolicGraphSaturation', 'DiophantineConsistency.CompactSameWitnessSaturation2', 'DiophantineConsistency.CompactPositionIncrement', 'DiophantineConsistency.CompactPositionGraph', 'DiophantineConsistency.CompactSelectorMask', 'DiophantineConsistency.CompactSelectorGraph', 'DiophantineConsistency.CompactSupportSlot', 'DiophantineConsistency.CompactCopySupport', 'DiophantineConsistency.CompactPeriodCopy', 'DiophantineConsistency.CompactSelectorPeriod', 'DiophantineConsistency.CompactCommonPeriodBits']
REPORTS={'DiophantineConsistency.FreeJGraphCongruenceExplore': ['FreeJGraphCongruenceExplore.fixed_symbolic_aligned', 'FreeJGraphCongruenceExplore.symbolic_aligned', 'FreeJGraphCongruenceExplore.first_pair_mod', 'FreeJGraphCongruenceExplore.graph_congruence', 'FreeJGraphCongruenceExplore.graph_aligned_congruence'], 'DiophantineConsistency.CompactSymbolicGraphSaturation': ['CompactSymbolicGraphSaturation.graph_saturation'], 'DiophantineConsistency.CompactSameWitnessSaturation2': ['CompactSameWitnessSaturation.fixed_graph_saturation', 'CompactSameWitnessSaturation.generic_graph_saturation'], 'DiophantineConsistency.CompactPositionIncrement': ['CompactPositionCarry.increment_digits'], 'DiophantineConsistency.CompactPositionGraph': ['CompactPositionCarry.generic_position_noCarry', 'CompactPositionCarry.fixed_position_noCarry'], 'DiophantineConsistency.CompactSelectorMask': ['CompactSelectorMask.selector_mask_digit', 'CompactSelectorMask.absent_mask_digit'], 'DiophantineConsistency.CompactSelectorGraph': ['CompactSelectorGraph.selector_slot', 'CompactSelectorGraph.excluded_slot', 'CompactSelectorGraph.fixed_graph_selector_bounds'], 'DiophantineConsistency.CompactSupportSlot': ['CompactSupportSlot.support_mask_digit', 'CompactSupportSlot.support_slot', 'CompactSupportSlot.fixed_graph_support_bounds'], 'DiophantineConsistency.CompactCopySupport': ['CompactCopySupport.position_good', 'CompactCopySupport.fixed_graph_copy_bounds'], 'DiophantineConsistency.CompactPeriodCopy': ['CompactPeriodCopy.period_index', 'CompactPeriodCopy.position_pos', 'CompactPeriodCopy.fixed_graph_period_copies'], 'DiophantineConsistency.CompactSelectorPeriod': ['CompactSelectorPeriod.period_index_zero_allowed', 'CompactSelectorPeriod.fixed_graph_period_selectors'], 'DiophantineConsistency.CompactCommonPeriodBits': ['CompactCommonPeriodBits.fixed_graph_common_period_bits']}
AXIOMS={'propext','Classical.choice','Quot.sound'}
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
    if not ok:raise ValueError(msg)
def git_head():return subprocess.run(['git','rev-parse','HEAD'],cwd=REPOSITORY,text=True,capture_output=True,check=True,timeout=10).stdout.strip()
def validate_reports(name,text):
    reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
    need(len(reports)==len(REPORTS[name]) and {r[0] for r in reports}==set(REPORTS[name]) and all({x.strip() for x in ax.split(',') if x.strip()}==({'propext','Quot.sound'} if n=='CompactPeriodCopy.position_pos' else AXIOMS) for n,ax in reports),('axiom reports',name,reports))
    return reports
def guard(stem):
    result={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            need(p.is_file(),('invalid companion',str(p)))
            result[str(p)]={'realpath':str(p.resolve()),'sha256':digest(p)}
        else:result[str(p)]=None
    return result
def checkguards(guards):
    for name,prior in guards.items():
        p=Path(name)
        if prior is None:need(not os.path.lexists(p),('unexpected companion',name))
        else:need(p.is_file() and str(p.resolve())==prior['realpath'] and digest(p)==prior['sha256'],('companion drift',name))
def mergeguards(allguards,new):
    for k,v in new.items():
        need(k not in allguards or allguards[k]==v,('inconsistent guard',k))
        allguards[k]=v
def check_output_location(obj,lib):
    need(not lib.is_symlink() and not lib.parent.is_symlink() and not lib.parent.parent.is_symlink() and not obj.parent.is_symlink() and obj.parent.resolve().is_relative_to(lib.resolve()),('invalid output directory',str(obj.parent)))
def output_guards(obj,before):
    stem=str(obj)[:-6]; result=guard(stem)
    for suffix in SUFFIXES:
        value=result[stem+suffix]
        if suffix=='.olean' and not before:need(value is not None and obj.is_file() and not obj.is_symlink(),('invalid emitted object',str(obj)))
        else:need(value is None,('unexpected output companion',stem+suffix))
    return result
def check_copy_destination(dst,frozen,out):
    # This is a point-in-time check; it does not make path traversal atomic.
    need(not out.is_symlink() and out.is_dir() and not frozen.is_symlink() and frozen.is_dir(),('invalid frozen root',str(frozen)))
    need(not dst.parent.is_symlink() and dst.parent.is_dir() and dst.parent.resolve().is_relative_to(frozen.resolve()),('invalid frozen source directory',str(dst.parent)))
    need(not os.path.lexists(dst) or (dst.is_file() and not dst.is_symlink()),('invalid frozen destination',str(dst)))
def check_frozen(rows):
    for name,src,sha,imports in rows:
        check_copy_destination(src,src.parent.parent,src.parent.parent.parent);need(src.is_file() and not src.is_symlink() and digest(src)==sha,('frozen source drift',name))
        need([line[7:] for line in src.read_text().splitlines() if line.startswith('import ')]==imports,('frozen imports drift',name))
def load_monitor():
    spec=importlib.util.spec_from_file_location('monitor',MONITOR);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def verify():
    for p,h in PINS.items():need(p.is_file() and digest(p)==h,('fixed input drift',str(p)))
    scan=json.loads((PLAN/'scan.json').read_bytes());parent=json.loads((PARENT_AUDIT/'CHECK.json').read_bytes());obs=json.loads((PARENT_AUDIT/'terminal-observation.json').read_bytes())
    need(scan['status']=='PRELIMINARY_COMMON_PERIOD_TWELVE_SOURCE_CLOSURE_NOT_A_BUILD' and [r['module'] for r in scan['source_order']]==MODULES and len(scan['objects']['author'])==150 and len(scan['objects']['peer'])==150 and len(scan['external_direct_slots'])==160 and len(scan['target_slots'])==240 and len(scan['init_slots'])==10,'invalid closure scan')
    need(parent['status']=='PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_PAIR_AUDIT' and type(parent['recorded_outer_exit']) is int and parent['recorded_outer_exit']==0 and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['lean_launched'] is False and obs['check_sha256']==PINS[PARENT_AUDIT/'CHECK.json'],'invalid parent receipt')
    closure=json.loads((CLOSURE_AUDIT/'CHECK.json').read_bytes());cobs=json.loads((CLOSURE_AUDIT/'terminal-observation.json').read_bytes())
    need(closure.get('status')=='PASS_INDEPENDENT_COMMON_PERIOD_SOURCE_CLOSURE' and closure.get('reviewed_commit')=='efd80cc5dc' and closure.get('source_modules')==12 and closure.get('parent_objects_per_side')==150 and closure.get('direct_slots')==160 and closure.get('target_slots')==240 and closure.get('init_slots')==10 and closure.get('source_report_counts')==[5,1,2,1,2,2,3,3,2,3,2,1] and type(cobs.get('observed_exit')) is int and cobs['observed_exit']==0 and cobs.get('lean_launched') is False and cobs.get('check_sha256')==PINS[CLOSURE_AUDIT/'CHECK.json'],'invalid closure receipt')
    run=subprocess.run([sys.executable,'-I','-S','-B',str(CLOSURE_AUDIT/'audit.py')],cwd=REPOSITORY,capture_output=True,timeout=300);need(run.returncode==0 and not run.stderr and json.loads(run.stdout)==closure,('closure review rerun',run.returncode,run.stderr))
    run=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=REPOSITORY,capture_output=True,timeout=180);need(run.returncode==0 and not run.stderr and run.stdout==(PLAN/'scan.json').read_bytes(),('closure scan rerun',run.returncode,run.stderr))
    run=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT_AUDIT/'audit.py')],cwd=REPOSITORY,capture_output=True,timeout=2400);need(run.returncode==0 and not run.stderr and json.loads(run.stdout)==parent,('parent audit rerun',run.returncode,run.stderr))
    for p,h in PINS.items():need(p.is_file() and digest(p)==h,('fixed input drift after audit',str(p)))
    return scan,parent

def validate_provider():
    need(PREFIX==Path('/tmp/ipra-direct-symbolic-k-pair-01'),('unexpected provider path',str(PREFIX)))
    external=('ArithmeticModularCancellation','CompactGraphDerivedRadix','CompactHighResidue','CompactLowEven','CompactLowExact','CompactMixedIncrement','CompactSymbolicKernel','FreeJConcreteDigitsClient')
    for side in ('author','peer'):
        lib=PREFIX/side/'lib';need(lib.is_dir() and not lib.is_symlink(),('missing provider library',str(lib)))
        for module in external:need((lib/'DiophantineConsistency'/(module+'.olean')).is_file(),('missing provider object',side,module))
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--verify-only',action='store_true');ap.add_argument('--expected-head',required=True);args=ap.parse_args()
    need(re.fullmatch('[0-9a-f]{40}',args.expected_head) is not None and git_head()==args.expected_head,'unexpected launch HEAD')
    need(not args.verify_only or args.output is None,'verify-only must not create output')
    if not args.verify_only:
        need(args.output is not None,'output required')
        out=args.output.absolute()
        need(out.parent.resolve(strict=True)==Path('/tmp').resolve() and out.name.startswith('ipra-common-period-pair-') and not os.path.lexists(out),'fresh direct /tmp output required')
    validate_provider();driver=digest(__file__);scan,parent=verify()
    need(git_head()==args.expected_head and digest(__file__)==driver,'HEAD drift or driver drift after preflight')
    if args.verify_only:
        print(json.dumps({'status':'PASS_COMMON_PERIOD_READ_ONLY_PREFLIGHT','driver_sha256':driver,'expected_head':args.expected_head,'source_modules':len(scan['source_order']),'parent_audit_status':parent['status'],'lean_launched':False}),flush=True)
        return
    need(shutil.disk_usage('/tmp').free>=4*1024**3,'sampled free space below reserve')
    monitor=load_monitor();out.mkdir();frozen=out/'frozen';frozen.mkdir();need(frozen.is_dir() and not frozen.is_symlink() and frozen.resolve().is_relative_to(out.resolve()),('invalid frozen root',str(frozen)));rows=[]
    for row in scan['source_order']:
        need(frozen.is_dir() and not frozen.is_symlink() and frozen.resolve().is_relative_to(out.resolve()),('invalid frozen root',str(frozen)))
        src=Path(row['source']);dst=(frozen/Path(*row['module'].split('.'))).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);check_copy_destination(dst,frozen,out);need(not os.path.lexists(dst),('source collision',str(dst)));shutil.copyfile(src,dst);check_copy_destination(dst,frozen,out)
        rows.append((row['module'],dst,row['source_sha256'],row['imports']))
    check_frozen(rows);runs=[];allguards={}
    for side in ('author','peer'):
        run=out/side;run.mkdir();lib=run/'lib';monitor.overlay(PREFIX/side/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
        for name,src,sha,imports in rows:
            need(git_head()==args.expected_head,'HEAD drift');need(shutil.disk_usage('/tmp').free>=4*1024**3,'sampled free space below reserve before child');check_frozen(rows);checkguards(allguards)
            obj=(lib/Path(*name.split('.'))).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            check_output_location(obj,lib)
            output_guards(obj,True)
            init=PACKAGE/'Init.olean';need(init.is_file(),'missing Init object');expected={str(init)}
            for dep in imports:
                candidate=(lib/Path(*dep.split('.'))).with_suffix('.olean')
                need(candidate.is_file(),('missing same-side project import',name,dep,str(candidate)))
                expected.add(str(candidate))
            guards={}
            for item in expected:mergeguards(guards,guard(item[:-6]))
            checkguards(guards);mergeguards(allguards,guards)
            deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
            lines=deps.stdout.splitlines()
            need(deps.returncode==0 and not deps.stderr and set(lines)==expected and 1<=lines.count(str(init))<=2 and all(lines.count(item)==1 for item in expected if item!=str(init)),('dependency mismatch',side,name,deps.returncode,deps.stdout,deps.stderr))
            checkguards(allguards);check_frozen(rows)
            cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)];log=run/(name.replace('.','_')+'.log')
            code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);output=log.read_text()
            need(type(code) is int and code==0 and reason is None and re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',output) is None,('compiler failure',side,name,code,reason,output[-8000:]))
            reports=validate_reports(name,output);check_output_location(obj,lib);mergeguards(allguards,output_guards(obj,False));checkguards(allguards);check_frozen(rows);need(shutil.disk_usage('/tmp').free>=4*1024**3,'sampled free space below reserve after child')
            steps.append({'module':name,'source_sha256':sha,'object_sha256':digest(obj),'log_sha256':digest(log),'stdout':output,'axiom_reports':reports,'compiler_exit':code,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd,'sampled_peak_rss_bytes':peak})
            (out/'progress.json').write_text(json.dumps({'completed':runs,'current':{'side':side,'steps':steps}},indent=2)+'\n')
        runs.append({'side':side,'steps':steps})
    strip=lambda row:{k:v for k,v in row.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')}
    need([strip(x) for x in runs[0]['steps']]==[strip(x) for x in runs[1]['steps']],'paired outputs differ')
    check_frozen(rows);checkguards(allguards);scan2,parent2=verify();check_frozen(rows);checkguards(allguards)
    need(scan2==scan and parent2==parent and digest(__file__)==driver and git_head()==args.expected_head,'final input or HEAD drift')
    for run in runs:
        for step in run['steps']:
            obj=Path(step['command'][-1]);log=out/run['side']/(step['module'].replace('.','_')+'.log')
            check_output_location(obj,out/run['side']/'lib')
            need(obj.is_file() and not obj.is_symlink() and digest(obj)==step['object_sha256'] and log.is_file() and not log.is_symlink() and digest(log)==step['log_sha256'],('final output drift',run['side'],step['module']))
    receipt={'status':'PASS_PAIRED_COMMON_PERIOD_BITS','runs':runs,'driver_sha256':driver,'protected_head':args.expected_head,'guards':allguards,'parent_audit':parent,'fixed_pins':{str(p):h for p,h in PINS.items()},'scope':'Fixed symbolic beta/low/high, arbitrary K and positive graph zero; selector, forbidden-selector and copy digit bounds for every period on the same N,w. No retained-byte port binding, graph-weighted decomposition, decoder, machine or internal iPRA proof. Parent package/transitive/dynamic, point-in-time and sampled-resource limitations remain.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'status':receipt['status'],'receipt_sha256':digest(out/'receipt.json')}),flush=True)
if __name__=='__main__':main()
