from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-compatible-provider-plan';result=h/'observations/plan-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(h/'plan.py')=='52b630774d0dd0e1a16cb44af620bcbef4090c53d7049c35cec88b5f58ee24c6' and sha(result)=='0a53a6330b8c45fa1830f21b2babc3847f9a46014a33f8db56578a8f9da00088'
p=json.loads(result.read_text());assert p['status']=='PASS' and p['root']=='Trace75FixedCongruence'
for path,d in p['inputs'].items():assert sha(path)==d
def load(s):return json.loads((root/'research'/s).read_text())
old=load('trace75-fresh-provider-plan/observations/plan-attempt01/result.json');scan=load('trace75-bfs-provider-preflight/observations/scan-attempt01/result.json');bfs=load('direct-bfs-80-coherent-rebuild/observations/attempt01/result.json');initial=load('direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json')
assert not set(initial)&set(bfs['built']);base=initial|bfs['built'];assert len(base)==1931
names=set(scan['roots']['Trace75FixedCongruence']['project']);headers=scan['headers'];assert len(names)==208
seeds=set(old['seeds'])|{'CarrierTransport','OffsetBound','PellFold','PellRankReduction','PellScaledSandwich','PellScaledUpper','PellVariableGrowth','TransportOrder'};assert seeds==set(p['seeds']) and len(seeds)==10 and seeds<=names
aff=set(seeds)
while 1:
 newer=aff|{n for n in names if aff.intersection(headers[n])}
 if newer==aff:break
 aff=newer
assert sorted(aff)==p['affected'];stages=(aff&names)-set(base);inherit=(aff&names)&set(base)-seeds
assert len(stages)==31 and len(inherit)==4 and stages==set(p['stage_order']) and sorted(inherit)==p['inherited_baseline_affected']
assert inherit=={'DiophantineConsistency.ModelArithmetic','DiophantineConsistency.ModelExponentialCongruence','PellOddFold','PellRecovery'}
for n in inherit:
 a=base[n]['.olean'];b=scan['selected_project'][n]['.olean'];assert a['sha256']==b['sha256'] and sha(a['path'])==a['sha256'];print('retained baseline',n,a['sha256'])
order=p['stage_order'];assert len(set(order))==31 and set(p['producers'])==stages
for i,n in enumerate(order):
 data=p['producers'][n];src=Path(data['source']);receipt=Path(data['receipt']);d=json.loads(receipt.read_text());snap=receipt.parent/'source.txt';out=receipt.parent/'stdout';err=receipt.parent/'stderr'
 assert sha(src)==sha(snap)==data['source_sha256'] and sha(receipt)==data['receipt_sha256'] and d['exit']==0 and d['reason'] is None and d['object_sha256']==data['object_sha256']==scan['selected_project'][n]['.olean']['sha256']
 assert sha(out)==d['stdout_sha256']==data['stdout_sha256'] and sha(err)==d['stderr_sha256']==data['stderr_sha256'] and not err.read_bytes() and not re.search(r'(?i)\b(?:warning|error)(?:\([^:\n]*\))?:|\bsorryAx\b',out.read_text())
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M); assert imports==[x for x in headers[n] if x!='Init'] and data['stage_imports']==[x for x in imports if x in stages] and all(order.index(m)<i for m in data['stage_imports'])
for n in p['preserved_bfs_overlap']:
 assert n in base and n in old['classification']['different'] and base[n]['.olean']['sha256']!=scan['selected_project'][n]['.olean']['sha256']
print('PASS 1931 baseline, 208 trace closure, 10 combined seeds, 31 absent source/receipt-matched topological stages, 4 same-hash inherited nodes')
