from pathlib import Path
import subprocess,hashlib,json,re,collections
D=Path(__file__).resolve().parents[2];root=D.parents[1];j=json.loads((D/'research/trace75-graph-support-331-inventory/observations/attempt02/stdout').read_text());f=json.loads((D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json').read_text());paths=sorted(x for x in subprocess.check_output(['rg','--files','Computability/DiophantineConsistency','-g','*.lean'],cwd=root,text=True).splitlines() if '/reviews/' not in x and '/observations/' not in x);idx=collections.defaultdict(list)
for q in paths:idx[Path(q).name].append(q)
changed=[]
for cat in ('basename_header_candidates','boundary_basename_header_candidates'):
 for n,old in j[cat].items():
  expected=sorted(set(f['serialized_headers'][n]) - {'Init'});new=[]
  for rel in idx[n.split('.')[-1]+'.lean']:
   p=root/rel;imp=sorted(set(re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)\s*(?:--.*)?$',p.read_text(errors='replace'),re.M)) - {'Init'})
   if imp==expected:new.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
  if new!=old:changed.append((n,len(old),len(new)))
assert not changed,changed
print('PASS current bounded 294-module candidate search agrees with captured lists')
print('captured HEAD',j['head'],'current HEAD',subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip());print('captured paths',j['rg_path_count'],'current paths',len(paths),'same digest',hashlib.sha256(('\n'.join(paths)+'\n').encode()).hexdigest()==j['rg_paths_sha256'])
