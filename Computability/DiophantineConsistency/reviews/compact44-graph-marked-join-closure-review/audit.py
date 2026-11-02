#!/usr/bin/env python3
"""Independent no-Lean, point-in-time source-plan audit, not a build."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('use isolated non-optimized Python')
P=pathlib.Path; root=P.cwd(); base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge'; plan=base/'compact44-graph-marked-join-plan'; scan=plan/'source-scan.json'
H=lambda p: hashlib.sha256(P(p).read_bytes()).hexdigest()
j=json.loads(scan.read_bytes()); rows=j['ordered_sources']; idx={r['module']:i for i,r in enumerate(rows)}
assert len(rows)==len(idx)==77 and not j['unresolved']
r=subprocess.run([sys.executable,'-I','-S','-B',str(plan/'scan.py')],cwd=root,capture_output=True,check=True,timeout=120)
assert not r.stderr and r.stdout==scan.read_bytes()
for i,row in enumerate(rows):
    p=root/row['source']; raw=p.read_bytes(); text=raw.decode(); imports=re.findall(r'^import\s+([\w.]+)',text,re.M)
    assert H(p)==row['sha256'] and imports==row['imports']
    assert all(len(line.split())==2 for line in text.splitlines() if line.startswith('import '))
    blob=subprocess.run(['git','show','3e57c2c7d1:'+row['source']],cwd=root,capture_output=True,check=True,timeout=60).stdout
    assert hashlib.sha256(blob).hexdigest()==row['sha256']
    for name in imports:
        if name.startswith('DiophantineConsistency.'):
            mod=name.split('.',1)[1]
            assert (mod in idx and idx[mod]<i) or mod in j['direct_inherited'], (row['module'],mod)
for item in j['direct_inherited'].values():
    p=P(item['path']); assert p.is_file() and str(p.resolve())==item['realpath'] and H(p)==item['sha256']
graph=P('/tmp/compact44-graph-support-join-01/lib'); package=P('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); historical=P('/tmp/ipra-compact-inverse-contextual-pair-01/author/lib/DiophantineConsistency'); rowparent=P('/tmp/ipra-compact-row-transport-pair-01/author/lib/DiophantineConsistency')
def inventory(p):
    files=list(p.glob('*.olean'));return {'slots':len(files),'dangling_symlinks':sum(x.is_symlink() and not x.exists() for x in files)}
inv={'graph':inventory(graph/'DiophantineConsistency'),'historical_inverse':inventory(historical),'historical_row_transport':inventory(rowparent)}
assert inv['graph']=={'slots':338,'dangling_symlinks':0}
assert inv['historical_inverse']=={'slots':786,'dangling_symlinks':473}
assert inv['historical_row_transport']=={'slots':785,'dangling_symlinks':473}
for side,item in j['model_difference_ring'].items():
    p=P(item['path']);assert p.is_file() and str(p.resolve())==item['realpath'] and H(p)==item['sha256']
assert j['model_difference_ring']['graph']['sha256']!=j['model_difference_ring']['historical']['sha256']
dangling={}
for n in ('ArithmeticWangPlane','ArithmeticWangRowStep'):
    p=historical/(n+'.olean'); assert p.is_symlink() and not p.exists();dangling[n]={'path':str(p),'target':str(p.resolve())}
frontier={}
for n in ('FixedGraphAnchoredMatch','CompactFieldCastBridge'):
    p=graph/'DiophantineConsistency'/(n+'.olean'); assert p.is_file();frontier[n]={'path':str(p),'realpath':str(p.resolve()),'sha256':H(p)}
externals={}
for n in j['other_direct_imports']:
    rel=n.replace('.','/')+'.olean'; paths=[p/rel for p in (graph,package)]
    externals[n]=[{'path':str(p),'exists':p.is_file(),'realpath':str(p.resolve()),'sha256':H(p) if p.is_file() else None} for p in paths]
assert len(externals)==19
for n in ('BusyBeaver.ZFC.ArithmeticMachineGraphPerm252','BusyBeaver.ZFC.ArithmeticMachineStepPerm252'):
    assert all(not x['exists'] for x in externals[n]);assert (root/'Computability/BusyBeaver/Lean'/P(*n.split('.'))).with_suffix('.lean').is_file()
assert all(externals[n][1]['exists'] for n in externals if n.startswith('Mathlib.'))
print(json.dumps({'status':'PASS_SOURCE_PLAN_REVIEW_WITH_MISSING_BUSYBEAVER_OBJECTS','reviewed_commit':'3e57c2c7d1','scan_sha256':H(scan),'scanner_rerun_exit':r.returncode,'source_count':len(rows),'topology_valid_for_listed_project_edges':True,'direct_inherited_count':len(j['direct_inherited']),'graph_frontier':frontier,'inventories':inv,'model_difference_ring':j['model_difference_ring'],'dangling_historical_modules':dangling,'external_imports':externals,'busybeaver_source_root':str(root/'Computability/BusyBeaver/Lean'),'lean_launched':False,'scope':'Point-in-time source/artifact inspection; no coherent build, transitive provider authentication, report sets, dependency query or paired replay.'},indent=2,sort_keys=True))
