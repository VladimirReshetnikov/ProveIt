"""Read-only source/provider union. No compiler, subprocess or new overlay."""
from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
OUT=D/'research/arithmetic-carrier-radix2011-cache-plan.json'
PROPOSAL=D/'research/arithmetic-carrier-radix2011-proposal.md'
pins={};comparisons=0

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def rec(p):
 p=Path(p);p=p if p.is_absolute()else R/p;b=p.read_bytes()
 return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global comparisons
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);need('bytes'not in x or a['bytes']==x['bytes'],'size '+x['path'])
 pins[a['path']]=a;comparisons+=1;return a
def load(relative,sha):
 p=check(dict(path=str(D/relative),sha256=sha));return p,json.loads(Path(p['path']).read_text())
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
 need(depth==0,'comments');s=''.join(o)
 return list(dict.fromkeys(([]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init'])+[n for l in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in l.split()]))
def leaf(packet_name,packet_sha,mf_name,mf_sha,module):
 pp,j=load('reviews/'+packet_name,packet_sha);mp,mf=load('reviews/'+mf_name,mf_sha)
 need(j['status']=='PASS','accepted status')
 for x in mf:check(x)
 for k in ['state','durable_state','driver','inputs','providers','final_authentication','freeze_authentication','author_packet','author_receipt','author_manifest']:
  if k in j:check(j[k])
 for row in j['records']:
  need(row['exit_code']==0,'accepted exit')
  for k in ['source','snapshot','object','log','timing']:check(row[k])
 row=next(x for x in j['records']if x['module']==module)
 return dict(module=module,source=check(row['source']),objects=[check(row['object'])],imports=imports(row['source']['path']),accepted_packet=pp,accepted_manifest=mp,provenance='Independently accepted new main leaf; exact final source/object/log/command and evidence manifest authenticated'),j

need(not OUT.exists(),'refuse overwrite');need(shutil.disk_usage('/tmp').free>=512*1024**2+8*1024**2,'reserve')
parent_pin,parent=load('research/arithmetic-carrier-soundness2011-cache-plan.json','f6672cfd5ef1d6d487fefb2060821cd7feb0c8b4b46644db215525535f1a8a8d')
for x in parent['pins']:check(x)
mods={x['module']:x for x in parent['modules']};bound={x['module']:x for x in parent['external']}
carrier,cpacket=leaf('arithmetic-carrier-soundness2011-root-replay.json','c166d8bf5c09c1faf80bc9c214608b04d01707ac9d1a0ae9430465760bb4cdb7','arithmetic-carrier-soundness2011-root-replay/FILES.json','a851c480a4448675693a0f3e0331b9fca5c73ff803689d6e0772413599ed74fc','DiophantineConsistency.ArithmeticCarrierSoundness2011')
power,ppacket=leaf('arithmetic-pell-power-recovery-root-replay.json','8c8a97aaa083bd02234c62c1fbeb4fe56092fd31a8cd02b6618706c6a5863f48','arithmetic-pell-power-recovery-root-replay/FILES.json','b5fc84bb906f3df1df77af65d0100106794fcd9f3cee0feade7d2ac98136deb6','DiophantineConsistency.ArithmeticPellPowerRecovery')
radix,rpacket=leaf('arithmetic-radix-alignment-peer-replay.json','d2ecc9d7e9890a16cd5b72fe99aba6433f49a6179ca7db7de8830816dc93058e','arithmetic-radix-alignment-peer-replay/FILES.json','38fce832944dd3a855b3d5649fdc4c0b354d5dbf4aefc96f35e6b8f7a8129172','DiophantineConsistency.ArithmeticRadixAlignment')
accept_pin,accept=load('reviews/arithmetic-radix-alignment-root-acceptance.json','75246f55f6187a9260939f5e0073639d15c8367519b3077b127f39996829edf3')
need(accept['status']=='PASS','radix ROOT acceptance')
for x in accept['pins']:check(x)
for m in [carrier,power,radix]:need(m['module']not in mods,'new leaf');mods[m['module']]=m
# Reconcile the complete overlapping radix parent, rather than merely its names.
radix_plan_pin,rp=load('research/arithmetic-radix-alignment-cache-plan.json','4c995d04b1f5a0f3bd72e068b7232d8f57f3f485f671f78dfc4a372c1b972558')
for x in rp['pins']:check(x)
overlaps=[]
for m in rp['modules']:
 old=mods[m['module']];check(m['source']);need(m['source']['sha256']==old['source']['sha256']and m['imports']==old['imports'],'overlap source/header')
 a={Path(x['path']).name:x['sha256']for x in m['objects']};b={Path(x['path']).name:x['sha256']for x in old['objects']};need(a==b,'overlap objects')
 for x in m['objects']:check(x)
 overlaps.append(dict(module=m['module'],source_sha256=m['source']['sha256'],artifact_hashes=a))
for m in rp['external']:
 old=bound[m['module']];check(m['source']);need(m['source']['sha256']==old['source']['sha256'],'boundary source overlap')
 need({Path(x['path']).name:x['sha256']for x in m['artifacts']}=={Path(x['path']).name:x['sha256']for x in old['artifacts']},'boundary artifact overlap')
 for x in m['artifacts']:check(x)
need(len(overlaps)==90,'all radix-parent overlaps')
seen=set();active=set();used=set();order=[]
def visit(n):
 if n not in mods:need(n in bound,'unknown boundary '+n);used.add(n);return
 if n in seen:return
 need(n not in active,'cycle');active.add(n);m=mods[n];check(m['source']);need(imports(m['source']['path'])==m['imports'],'header '+n)
 for child in m['imports']:visit(child)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
direct=[m['module']for m in [carrier,power,radix]]
for n in direct:visit(n)
need(seen==set(mods)and used==set(bound),'exact union')
external=[bound[n]for n in sorted(used)]
for m in external:
 check(m['source'])
 for x in m['artifacts']:check(x)
need(parent['compiler']['sha256']==rp['compiler']['sha256'],'same compiler');check(parent['compiler'])
need(parent['boundary_search']==rp['boundary_search'],'same explicit package search')
search=[cpacket['provider'],ppacket['private_provider'],rpacket['private_provider'],*parent['boundary_search']]
providers=[]
for m in [mods[n]for n in order]+external:
 for obj in m.get('objects',m.get('artifacts')):
  rel=Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
  actual=next((Path(p)/rel for p in search if(Path(p)/rel).is_file()),None)
  need(actual is not None,'missing provider '+str(rel))
  providers.append(dict(module=m['module'],relative=str(rel),expected=obj,actual=check(dict(obj,path=str(actual)))))
counts=dict(custom=len(order),Foundation=sum(n.startswith('Foundation.')for n in order),artifacts=sum(len(mods[n]['objects'])for n in order),external=len(external),boundary_primaries=len(external),boundary_companions=sum(len(m['artifacts'])-1 for m in external),boundary_artifacts=sum(len(m['artifacts'])for m in external),actual_first_providers=len(providers),fresh_prerequisites=0)
need(counts==dict(custom=138,Foundation=95,artifacts=423,external=50,boundary_primaries=50,boundary_companions=100,boundary_artifacts=150,actual_first_providers=573,fresh_prerequisites=0),'exact scope')
receipts=[check(rec(D/('reviews/'+n)))for n in ['arithmetic-carrier-soundness2011-root.md','arithmetic-pell-power-recovery-root.md','arithmetic-radix-alignment-root.md']]
check(rec(PROPOSAL));check(rec(__file__))
for x in list(pins.values()):check(x)
need(shutil.disk_usage('/tmp').free>=512*1024**2+8*1024**2,'output reserve')
j=dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',scope='Proposed actual maintained positive/natural split zero to accepted power and actual 94517-aligned radix, with no synthetic norm/transport/port/index/power premises. No new proof is compiled here.',proposal=rec(PROPOSAL),auditor=rec(__file__),parent=parent_pin,radix_parent=radix_plan_pin,radix_root_acceptance=accept_pin,accepted_receipts=receipts,direct_imports=direct,counts=counts,modules=[mods[n]for n in order],topological_order=order,overlaps=overlaps,external=external,compiler=parent['compiler'],boundary_search=parent['boundary_search'],audited_existing_search=search,first_providers=providers,pins=list(pins.values()),comparisons=comparisons,unique_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free,cache_scope='Three accepted main leaves added to exact accepted carrier DAG; no prerequisite compiled, no new package boundary, no broad package/source rebuild claim.')
OUT.write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps(dict(plan=rec(OUT),proposal=rec(PROPOSAL),auditor=rec(__file__),counts=counts,comparisons=comparisons,paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free),indent=2))
