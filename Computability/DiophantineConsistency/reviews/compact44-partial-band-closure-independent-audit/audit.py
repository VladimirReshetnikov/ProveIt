#!/usr/bin/env python3
"""Independent no-Lean partial-band source and same-side provider review."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S -B, without optimization')
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
R=BASE/'research/ordinary12-ipra-bridge'
PLAN=R/'compact44-partial-band-closure-plan'
SOURCE=R/'compact44-partial-band-prototype/CompactPartialBand.lean'
PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01')
AUDIT=BASE/'reviews/compact44-coefficient-decomposition-independent-audit'
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={PLAN/'README.md':'87c09ffc153c7b3a903de05e80d469d217ebee16df39169f299eb57cff0993b9',PLAN/'scan.py':'2e839fe0350645a0348958d18b279218b6464c9ec151b0c0a1e279ff65082801',PLAN/'scan.json':'448e3d7be056a54908a0d79f5b5e1dce186d209b96fa752b28414cc1f3abde0d',PLAN/'terminal-observation.json':'a203f6e6d86eeddc86fd8026855f6b8927086e02195d3a0c6e1fd9839cf3645e',SOURCE:'26b73b92c91baef599ab9d473965af940b9b39ae81d76f0979ed80129109ba0f',AUDIT/'audit.py':'389e92b0a29c342e39b0f9ad2fd6b4e2d7e42245433ceda24a613670492c55ff',AUDIT/'CHECK.json':'2351c55148f2e3eb4b8ac51894050dbfd942eef7fdad26030251cbf637e94432',AUDIT/'terminal-observation.json':'05ee4dbdf225dca03ed312273d325942f45e6770878cb3f6ba341fa34093a665'}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def slots(stem):
    result={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            need(p.is_file(),('invalid slot',str(p)))
            result[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
        else:result[str(p)]=None
    return result
def main():
    prefix=PLAN.relative_to(ROOT).as_posix()+'/'
    names=subprocess.run(['git','ls-tree','-r','--name-only','7ae590be72','--',prefix],cwd=ROOT,capture_output=True,text=True,check=True,timeout=30).stdout.splitlines()
    need(len(names)==4,'plan evidence inventory')
    for name in names:
        b=subprocess.run(['git','show','7ae590be72:'+name],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
        need(hashlib.sha256(b).hexdigest()==H(ROOT/name),('plan committed bytes',name))
    blob=subprocess.run(['git','show','7dea2a8f40:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
    need(hashlib.sha256(blob).hexdigest()==H(SOURCE),'source committed bytes')
    for p,h in PINS.items():need(p.is_file() and H(p)==h,('fixed pin',str(p)))
    scan=json.loads((PLAN/'scan.json').read_bytes());obs=json.loads((PLAN/'terminal-observation.json').read_bytes())
    need(scan['status']=='PRELIMINARY_PARTIAL_BAND_SOURCE_CLOSURE_NOT_A_BUILD' and scan['source_commit']=='7dea2a8f40' and scan['source_sha256']==PINS[SOURCE] and scan['source']==str(SOURCE),'scan identity')
    need(obs=={'status':scan['status'],'normal_session':78570,'normal_observed_exit':0,'optimized_observed_exit':1,'scan_sha256':PINS[PLAN/'scan.json'],'lean_launched':False},'recorded scan observation')
    text=SOURCE.read_text();imports=[line[7:] for line in text.splitlines() if line.startswith('import ')]
    need(imports==scan['imports']==['DiophantineConsistency.CompactCoefficientDecoder','DiophantineConsistency.ArithmeticCyclicWord'],'imports')
    reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M)
    need(reports==scan['axiom_reports']==['CompactPartialBand.band_decomposition'],'report names')
    need('theorem band_decomposition (pos : Fin 41 → ℕ) (T : ℕ) (n C k : V)' in text and '(hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n))' in text and 'dig_rot 67 n C' in text and 'CompactCoefficientDecoder.finite_decomposition' in text,'theorem scope')
    check=json.loads((AUDIT/'CHECK.json').read_bytes());term=json.loads((AUDIT/'terminal-observation.json').read_bytes())
    need(check['status']=='PASS_INDEPENDENT_COEFFICIENT_DECOMPOSITION_PAIR_AUDIT' and type(term['observed_exit']) is int and term['observed_exit']==0 and term['lean_launched'] is False and term['check_sha256']==PINS[AUDIT/'CHECK.json'] and scan['parent_audit_sha256']==PINS[AUDIT/'CHECK.json'],'parent receipt')
    normal=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,timeout=180)
    need(normal.returncode==0 and not normal.stderr and normal.stdout==(PLAN/'scan.json').read_bytes(),('scan rerun',normal.returncode,normal.stderr[-1000:]))
    opt=subprocess.run([sys.executable,'-O','-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,timeout=180)
    need(opt.returncode==1 and not opt.stdout and b'requires nonoptimized' in opt.stderr,'optimized scan rejected')
    libs=[PARENT/side/'lib' for side in ('author','peer')]
    inv=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs]
    need(len(inv[0])==126 and set(inv[0])==set(inv[1]),'provider object inventories')
    need(len(scan['objects'])==126 and len({row['path'] for row in scan['objects']})==126,'recorded inventory')
    for row in scan['objects']:
        rel=row['path'];need(rel in inv[0] and H(inv[0][rel])==H(inv[1][rel])==row['sha256'] and str(inv[0][rel].resolve())==row['author_resolved'] and str(inv[1][rel].resolve())==row['peer_resolved'],('provider object',rel))
    direct={};targets={}
    for lib in libs:
        for name in ('CompactCoefficientDecoder','ArithmeticCyclicWord'):
            stem=lib/'DiophantineConsistency'/name
            need(Path(str(stem)+'.olean').is_file(),('required object',str(stem)))
            direct.update(slots(stem))
        target=slots(lib/'DiophantineConsistency/CompactPartialBand')
        need(all(value is None for value in target.values()),('occupied target',str(lib)))
        targets.update(target)
    init=slots(PACKAGE/'Init')
    need(Path(str(PACKAGE/'Init')+'.olean').is_file() and len(direct)==40 and len(targets)==20 and len(init)==10,'slot counts')
    need(direct==scan['direct_slots'] and targets==scan['target_slots'] and init==scan['init_slots'],'slot inventories')
    parent=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],cwd=ROOT,capture_output=True,timeout=1800)
    need(parent.returncode==0 and not parent.stderr and json.loads(parent.stdout)==check,('parent audit rerun',parent.returncode,parent.stderr[-1500:]))
    print(json.dumps({'status':'PASS_INDEPENDENT_PARTIAL_BAND_SOURCE_CLOSURE','plan_commit':'7ae590be72','source_commit':'7dea2a8f40','source_sha256':PINS[SOURCE],'provider_objects_per_side':126,'direct_companion_slots':40,'absent_target_slots':20,'init_slots':10,'normal_scan_exit':normal.returncode,'optimized_scan_exit':opt.returncode,'parent_audit_rerun_exit':parent.returncode,'reviewer_authored_lean_source':True,'lean_launched':False,'scope':'Point-in-time source and same-side provider review; reviewer authored the Lean source but did not author the closure scan. This is not a paired build or a proof of full graph column, temporal alignment, retained K, no-carry premises, machine semantics or iPRA equivalence. Parent package/transitive/dynamic ancestry and between-check limitations remain.'},indent=2))
if __name__=='__main__':main()
