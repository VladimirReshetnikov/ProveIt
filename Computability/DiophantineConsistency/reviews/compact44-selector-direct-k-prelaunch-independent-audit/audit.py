#!/usr/bin/env python3
"""Point-in-time independent no-Lean review of two paired replay drivers."""
import hashlib, importlib.util, json, os, re, subprocess, sys, tempfile
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S -B, without optimization')
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge'
HERE=Path(__file__).resolve().parent
HEAD='4903bf45b6c509358155beb8f70feac7a908b7d2'
CASES=(
 ('selector','compact44-selector-graph-pair-prototype','7fee5168b4','f6a4b8321fa2c532d55c6816d5fbd7c9ebe981604949c1695340f965f3525117','/tmp/ipra-same-witness-saturation-pair-01',4,8,'eca415e5e567f4b280fdc9e67b285785193c12d8bd8e0fc5db3182c3ac753518','PASS_SELECTOR_GRAPH_READ_ONLY_PREFLIGHT',16122),
 ('direct_k','compact44-direct-symbolic-k-pair-prototype','840ce4adb1','dc56ea8855a5a332e2481509e40f28813f17dc6f3f60056e70c09d355b2b8d2c','/tmp/ipra-compact-graph-derived-radix-pair-01',7,17,'a941858afe34f48a5d21a2349a90a8a7abf7c28a2b1e4b5f97e1f290a454d830','PASS_DIRECT_SYMBOLIC_K_READ_ONLY_PREFLIGHT',48741))
def need(ok,msg):
    if not ok:raise ValueError(msg)
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def reject(f,what):
    try:f()
    except ValueError:return
    raise ValueError('accepted '+what)
def main():
    results=[]
    for label,folder,rev,want,prefix,count,reports,fake_sha,status,session in CASES:
        pkg=BASE/folder;driver=pkg/'replay.py';rel=driver.relative_to(ROOT).as_posix()
        committed=subprocess.run(['git','show',rev+':'+rel],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
        need(H(driver)==want==hashlib.sha256(committed).hexdigest(),(label,'driver bytes'))
        spec=importlib.util.spec_from_file_location('independent_'+label,driver);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        need(str(m.PREFIX)==prefix,(label,'provider path'))
        for p,h in m.PINS.items():need(p.is_file() and H(p)==h,(label,'fixed pin',str(p)))
        scan=json.loads((m.PLAN/'scan.json').read_bytes());need([x['module'] for x in scan['source_order']]==m.MODULES and len(m.MODULES)==count,(label,'source order'))
        for row in scan['source_order']:
            src=Path(row['source']);need(src.is_file() and H(src)==row['source_sha256'],(label,'source',str(src)))
            need([x[7:] for x in src.read_text().splitlines() if x.startswith('import ')]==row['imports'],(label,'imports',row['module']))
            names=re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M)
            need(len(names)==len(m.REPORTS[row['module']]) and set(names)==set(m.REPORTS[row['module']]),(label,'report names',row['module']))
        need(sum(len(x) for x in m.REPORTS.values())==reports,(label,'report count'))
        if label=='selector':m.validate_provider()
        for side in ('author','peer'):
            lib=m.PREFIX/side/'lib';need(lib.is_dir() and not lib.is_symlink(),(label,'provider',str(lib)))
            for row in scan['source_order']:
                obj=(lib/Path(*row['module'].split('.'))).with_suffix('.olean');stem=str(obj)[:-6]
                for ext in m.SUFFIXES:need(not os.path.lexists(stem+ext),(label,'target occupied',stem+ext))
        recorded=json.loads((pkg/'corrected-preflight-observation.json').read_bytes());pre=(pkg/'corrected-preflight.json').read_bytes()
        need(type(recorded['observed_exit']) is int and recorded['observed_exit']==0 and recorded['stderr_bytes']==0 and recorded['lean_launched'] is False and recorded['driver_sha256']==want and recorded['stdout_sha256']==hashlib.sha256(pre).hexdigest(),(label,'author preflight observation'))
        author=json.loads(pre);need(author['driver_sha256']==want and author['expected_head']==recorded['head'] and author['lean_launched'] is False,(label,'author preflight content'))
        independent=json.loads((HERE/(label+'-independent-preflight.json')).read_bytes())
        need(independent['status']==status and independent['driver_sha256']==want and independent['expected_head']==HEAD and independent['source_modules']==count and independent['lean_launched'] is False,(label,'independent preflight'))
        run=subprocess.run([sys.executable,'-I','-S','-B',str(m.PLAN/'scan.py')],cwd=ROOT,capture_output=True,timeout=180)
        need(run.returncode==0 and not run.stderr and run.stdout==(m.PLAN/'scan.json').read_bytes(),(label,'source scan',run.returncode,run.stderr[-1000:]))
        opt=subprocess.run([sys.executable,'-O','-I','-S','-B',str(m.PLAN/'scan.py')],cwd=ROOT,capture_output=True,timeout=180)
        need(opt.returncode!=0,(label,'optimized scan accepted'))
        fake=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'fake-controls.py')],cwd=ROOT,capture_output=True,timeout=180)
        need(fake.returncode==0 and not fake.stderr and hashlib.sha256(fake.stdout).hexdigest()==fake_sha and fake.stdout==(pkg/'fake-controls.log').read_bytes(),(label,'fake controls',fake.returncode,fake.stderr[-1000:]))
        # Independent local checks, in addition to the author's full fake loop.
        with tempfile.TemporaryDirectory(prefix='ipra-independent-driver-check-',dir='/tmp') as td:
            out=Path(td)/'out';frozen=out/'frozen';directory=frozen/'DiophantineConsistency';directory.mkdir(parents=True)
            dst=directory/'Source.lean';dst.write_text('import Example\n');m.check_copy_destination(dst,frozen,out)
            dst.unlink();dst.symlink_to(Path(td)/'missing');reject(lambda:m.check_copy_destination(dst,frozen,out),label+' frozen file symlink');dst.unlink()
            directory.rename(Path(td)/'actual');directory.symlink_to(Path(td)/'actual',target_is_directory=True)
            reject(lambda:m.check_copy_destination(dst,frozen,out),label+' frozen directory symlink')
            obj=Path(td)/'Obj.olean'
            for ext in m.SUFFIXES:
                sidecar=Path(str(obj)[:-6]+ext);sidecar.write_bytes(b'x')
                reject(lambda:m.output_guards(obj,True),label+' preexisting '+ext)
                sidecar.unlink()
            obj.write_bytes(b'object');m.output_guards(obj,False)
            for ext in m.SUFFIXES:
                if ext=='.olean':continue
                sidecar=Path(str(obj)[:-6]+ext);sidecar.write_bytes(b'x');reject(lambda:m.output_guards(obj,False),label+' emitted '+ext);sidecar.unlink()
            obj.unlink();obj.symlink_to(dst);reject(lambda:m.output_guards(obj,False),label+' output symlink')
        for module in m.MODULES:
            expected=m.REPORTS[module]
            mapping={name:m.AXIOMS for name in expected} if label=='selector' else expected
            lines=[]
            for name,ax in sorted(mapping.items()):
                lines.append("'%s' depends on axioms: [%s]"%(name,', '.join(sorted(ax))) if ax else "'%s' does not depend on any axioms"%name)
            good='\n'.join(lines)+'\n';m.validate_reports(module,good)
            reject(lambda:m.validate_reports(module,good+lines[0]+'\n'),label+' duplicate axiom report')
            reject(lambda:m.validate_reports(module,good.replace(lines[0],"'bogus' does not depend on any axioms",1)),label+' wrong axiom report')
        results.append({'label':label,'driver_sha256':want,'provider':prefix,'pinned_inputs':len(m.PINS),'sources':count,'named_reports':reports,'fake_sha256':fake_sha,'independent_preflight_session':session,'independent_preflight_exit':0,'independent_preflight_head':HEAD,'normal_scan_exit':run.returncode,'optimized_scan_exit':opt.returncode,'independent_local_guards':'PASS'})
    print(json.dumps({'status':'PASS_INDEPENDENT_SELECTOR_DIRECT_K_PRELAUNCH','results':results,'scope':'No Lean build. Fixed pins and source declarations, recorded and independent preflights, authored full fake controls and separate point-in-time local guards reviewed. Real builds still require clean initial loader, externally stable HEAD, sole Lean, fresh output and independent artifact audits. Source-copy and companion checks are point-in-time, not atomic; sampled resource, dependency-query and inherited package/transitive/dynamic ancestry limitations remain. No retained-tuple, machine or iPRA claim.'},indent=2))
if __name__=='__main__':main()
