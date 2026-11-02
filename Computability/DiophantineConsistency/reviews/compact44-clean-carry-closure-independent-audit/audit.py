from pathlib import Path
import hashlib,json,os,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
root=Path(__file__).resolve().parents[4];base=root/'Computability/DiophantineConsistency';plan=base/'research/ordinary12-ipra-bridge/compact44-clean-carry-closure-plan';r=json.loads((plan/'scan.json').read_text());H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('README.md','scan.py','scan.json'):
 p=plan/name;rel=p.relative_to(root).as_posix();blob=subprocess.run(['git','show','8a5840d47b:'+rel],cwd=root,capture_output=True,check=True).stdout;assert blob==p.read_bytes(),name
q=subprocess.run([sys.executable,'-I','-S','-B',str(plan/'scan.py')],capture_output=True,timeout=120,check=True);assert not q.stderr and json.loads(q.stdout)==r
parent=base/'reviews/compact44-heterogeneous-carry-independent-audit/CHECK.json';assert H(parent)=='415d5b4056e35eda01b7896c330d9298af4a410fffca31edad12fe902afd11f9';audit=json.loads(parent.read_bytes());assert audit['status']=='PASS_INDEPENDENT_COMPACT44_HETEROGENEOUS_CARRY_AUDIT' and type(audit['recorded_outer_exit']) is int and audit['recorded_outer_exit']==0
libs=[Path('/tmp/ipra-compact-heterogeneous-carry-pair-01')/s/'lib' for s in ('author','peer')];inventories=[]
for lib in libs:inventories.append({p.relative_to(lib).as_posix():H(p) for p in lib.rglob('*.olean') if p.is_file()})
assert inventories[0]==inventories[1] and len(inventories[0])==115 and inventories[0]=={v['module_path']:v['sha256'] for v in r['inherited_objects']}
for x in r['inherited_objects']:
 rel=Path(x['module_path']);assert str((libs[0]/rel).resolve())==x['author_resolved_path'] and str((libs[1]/rel).resolve())==x['peer_resolved_path']
for side,lib in zip(('author','peer'),libs):
 item=next(x for x in r['seeds'] if x['side']==side);record=next(x for x in audit['runs'] if x['side']==side);seed=Path('/tmp/ipra-compact-heterogeneous-carry-pair-01')/side/'CompactHeterogeneousCarry.olean';assert seed.is_file() and H(seed)==item['sha256']==record['object_sha256'] and str(seed.resolve())==item['resolved_path'];assert not os.path.lexists(lib/item['target_relative_path']);assert not os.path.lexists(lib/'DiophantineConsistency/CompactCarryReset.olean')
client=r['client'];src=Path(client['source']);assert H(src)==client['source_sha256']=='f80d473cb579a24086ae29e560cce33a8ed282bf90ce7458302ec8a3d244928d';text=src.read_text();assert [v for l in text.splitlines() if l.startswith('import ') for v in l[7:].split()]==client['imports']==['DiophantineConsistency.CompactHeterogeneousCarry']
for token in ('[Fintype ι]','(h : CarryInput w n F b D a X)','(hk : k < n)','(hpred :','(ht :','(hroom :','(hbase :','(htarget :','theorem clean_after_bounded_predecessor','theorem digit_after_bounded_predecessor'):assert token in text,token
init=Path(r['package_init']['path']);assert init.is_file() and H(init)==r['package_init']['sha256'] and str(init.resolve())==r['package_init']['resolved_path']
print(json.dumps({'status':'PASS_INDEPENDENT_CLEAN_CARRY_SOURCE_CLOSURE','reviewed_commit':'8a5840d47b','inherited_objects_per_side':115,'same_side_seed_hashes_checked':2,'client_import_count':1,'scope':'Point-in-time source, seed and olean inventory only; no full parent audit rerun, atomic freeze, all companion slots, paired Lean build, graph/rotation conditions, checker, machine or PRA proof.'},indent=2))
