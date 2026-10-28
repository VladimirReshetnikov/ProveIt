from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';H=D/'research'
O=H/'arithmetic-pell-auxiliary-seed-cache-plan.json'
pins={};observations=0

def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);assert a['sha256']==x['sha256'],x['path']
 if 'bytes' in x:assert a['bytes']==x['bytes'],x['path']
 pins[a['path']]=a;observations+=1;return a
def imports(p):
 s=Path(p).read_text();o=[];i=depth=0
 while i<len(s):
  t=s[i:i+2]
  if depth:
   if t=='/-':depth+=1;i+=2
   elif t=='-/':depth-=1;i+=2
   else:o.append('\n'if s[i]=='\n'else' ');i+=1
  elif t=='/-':depth=1;i+=2
  elif t=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 assert depth==0;s=''.join(o)
 return list(dict.fromkeys(([]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init'])+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in line.split()]))
assert not O.exists();assert shutil.disk_usage('/tmp').free>=512*1024**2
parents=[]
for name in ['arithmetic-pell-half-index-cache-plan.json','arithmetic-pell-squared-seed-cache-plan.json']:
 p=H/name;parents.append(check(rec(p)))
plans=[json.loads(Path(p['path']).read_text())for p in parents]
for j in plans:
 for x in j['pins']:check(x)
mods={m['module']:m for m in plans[0]['modules']};overlaps=[]
for m in plans[1]['modules']:
 n=m['module'];old=mods.get(n)
 if old:
  assert old['source']['sha256']==m['source']['sha256'],n
  ao={Path(x['path']).name:x['sha256']for x in old['objects']};bo={Path(x['path']).name:x['sha256']for x in m['objects']}
  assert ao==bo,n;overlaps.append(dict(module=n,source=m['source']['sha256'],artifacts=ao))
 else:mods[n]=m
external={m['module']:m for m in plans[0]['external']}
for m in plans[1]['external']:
 old=external[m['module']];assert old['source']['sha256']==m['source']['sha256']
 assert {Path(x['path']).name:x['sha256']for x in old['artifacts']}=={Path(x['path']).name:x['sha256']for x in m['artifacts']}
accepted=[]
for name,mf,rootnote in [
 ('arithmetic-pell-half-index-root-replay.json','arithmetic-pell-half-index-root-replay/FILES.json','arithmetic-pell-half-index-root.md'),
 ('arithmetic-pell-squared-seed-peer-replay.json','arithmetic-pell-squared-seed-peer-replay/FILES.json','arithmetic-pell-squared-seed-root.md')]:
 p=D/'reviews'/name;pk=check(rec(p));j=json.loads(p.read_text());f=D/'reviews'/mf;fr=check(rec(f));manifest=json.loads(f.read_text())
 for x in manifest:
  path=Path(x['path']);path=path if path.is_absolute()else R/path
  check({**x,'path':str(path)})
 note=check(rec(D/'reviews'/rootnote));row=j['records'][0]
 assert row['exit_code']==0;source=check(row['source']);obj=check(row['object']);check(row['snapshot']);check(row['log']);check(row['timing'])
 n=row['module'];mods[n]=dict(module=n,source=source,objects=[obj],imports=imports(source['path']),provenance=dict(accepted_packet=pk,manifest=fr,root_note=note,compiler_record=row))
 accepted.append(dict(module=n,packet=pk,manifest=fr,root_note=note,selected_object=obj))
check(rec(D/'reviews/arithmetic-pell-squared-seed-root-acceptance.json'))
direct=['DiophantineConsistency.ArithmeticPellSquaredSeed','DiophantineConsistency.ArithmeticPellHalfIndex']
seen=set();active=set();used=set();order=[]
def visit(n):
 if n not in mods:assert n in external,n;used.add(n);return
 if n in seen:return
 assert n not in active,n;active.add(n);m=mods[n];check(m['source']);actual=imports(m['source']['path']);assert actual==m['imports'],n
 for c in actual:visit(c)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
for n in direct:visit(n)
assert seen==set(mods);assert used==set(external)
search=['/tmp/arithmetic-pell-half-index-root-qso00172/lib','/tmp/pell-squared-seed-controller-peer-n40xllwf/lib',*plans[0]['boundary_search']]
providers=[]
for m in [mods[n]for n in order]+[external[n]for n in sorted(used)]:
 check(m['source'])
 for obj in m.get('objects',m.get('artifacts',[])):
  check(obj);rel=Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
  p=next((Path(q)/rel for q in search if(Path(q)/rel).is_file()),None);assert p is not None,str(rel)
  a=check(dict(obj,path=str(p)));providers.append(dict(module=m['module'],relative=str(rel),expected=obj,actual=a))
counts=dict(custom=len(mods),Foundation=sum(n.startswith('Foundation.')for n in mods),artifacts=sum(len(m['objects'])for m in mods.values()),external=len(external),boundary_primaries=len(external),boundary_companions=sum(len(m['artifacts'])-1 for m in external.values()),actual_first_providers=len(providers),fresh_prerequisites=0)
assert counts==dict(custom=108,Foundation=95,artifacts=393,external=38,boundary_primaries=38,boundary_companions=76,actual_first_providers=507,fresh_prerequisites=0)
assert len(overlaps)==99
check(plans[0]['compiler']);check(rec(__file__))
for x in list(pins.values()):check(x)
result=dict(status='READ_ONLY_PROPOSAL_NO_LEAN_OVERLAY_OR_COMPILER',direct_imports=direct,parents=parents,accepted_mains=accepted,counts=counts,modules=[mods[n]for n in order],topological_order=order,external=[external[n]for n in sorted(used)],boundary_search=plans[0]['boundary_search'],provider_search=search,compiler=plans[0]['compiler'],overlap_comparisons=overlaps,first_providers=providers,pins=list(pins.values()),observations=observations,unique_paths=len(pins),auditor=rec(__file__),scope='Oriented actual f-squared and ordinate residues at rank three modulo four; positive full fourteen-variable auxiliary witnesses from accepted squared seed. No outer simultaneous witnesses, signed thirteen-variable carrier or final HA claim.')
O.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(plan=rec(O),counts=counts,observations=observations,unique_paths=len(pins)),indent=2))
