from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[2]; R=root/'research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
paths={'pref':Path('/tmp/trace75-reverse-fresh-preflight.json'),'fresh':R/'trace75-fresh-provider-rebuild/observations/attempt01/result.json','base':R/'direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json','bfs':R/'direct-bfs-80-coherent-rebuild/observations/attempt01/result.json','scan':R/'trace75-bfs-provider-preflight/observations/scan-attempt01/result.json'}
hashes={'pref':'6362d0875bb7fcda0630da48aa3fbb403d1f9881260ccb4d932638c7cf8fee78','fresh':'b74858343a05be6710e0666abb86189aea375ebd4d494411fee00d31e9f31e1a','base':'a89c775deee5d7f846e85936f2321c1e91d3d5fd51c62b153c2b2dd8e8540f88','bfs':'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559','scan':'e27f1cb8694aab43a1023abcce95f7fbc7846d4860dac4b96046391da3dd1e8d'}
for n,p in paths.items():assert sha(p)==hashes[n]
data={n:json.loads(p.read_text()) for n,p in paths.items()}; pre=data['pref']['overlaps']; fresh=data['fresh']; base=data['base']; bfs=data['bfs']['closure']['project']; fg=fresh['serialized_headers']; bg={n:x['imports'] for n,x in bfs.items()}
expected={'CarrierTransport','OffsetBound','PellFold','PellRankReduction','PellScaledSandwich','PellScaledUpper','PellVariableGrowth','TransportOrder'}; assert set(pre)==expected
def closure(root,g):
 seen=set();todo=[root]
 while todo:
  x=todo.pop()
  if x not in seen:seen.add(x);todo.extend(g.get(x,[]))
 return seen
bc=closure('DirectBFSHaltPellSeed',bg);fc=closure('Trace75FixedCongruence',fg); assert expected<=bc and len(bc & bfs.keys())==855 and len(fc & fg.keys())==208
for n in sorted(expected):
 p=pre[n]; old=base[n]['.olean']; new=fresh['selected_project'][n]['.olean']; b=bfs[n]['record']
 assert old['sha256']==p['replaced_base']['.olean']==b['sha256'] and new['sha256']==p['selected_supplement']['.olean'] and old['sha256']!=new['sha256']
 for k,v in p['replaced_base'].items():assert v==(base[n][k]['sha256'] if base[n][k] else None)
 for k,v in p['selected_supplement'].items():assert v==(fresh['selected_project'][n][k]['sha256'] if fresh['selected_project'][n][k] else None)
 assert sha(old['path'])==old['sha256'] and sha(new['path'])==new['sha256']
 print(n,'BFS',old['sha256'],'trace75',new['sha256'])
affected=set(expected)
while True:
 n=affected|{x for x in fc if affected.intersection(fg.get(x,[]))}
 if n==affected:break
 affected=n
stages=set(fresh['stage_order']); assert len(stages)==14 and len(affected&stages)==13 and stages-affected=={'Trace75ProductHeight'}
other=affected-expected-stages;assert len(other)==19 and len(affected)==40
print('BFS captured project closure:',len(bc & bfs.keys()),'; trace75 captured project closure:',len(fc & fg.keys()))
print('Preserve 8 BFS seeds; rebuild affected:',len(affected-expected),'=',len(affected&stages),'previous replay stages +',len(other),'other selected modules')
print('Unaffected previous stage:',','.join(stages-affected));print('Other affected:',', '.join(sorted(other)))
