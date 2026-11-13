#!/usr/bin/env python3
"""Independent Horner reconstruction and retained-evidence audit; no Lean launch."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import ast,gzip,hashlib,json,os,re
from pathlib import Path
HERE=Path(__file__).resolve().parent; TASK=HERE.parents[1]
P=TASK/'research/current2011-kernel-byte-recipe'
def sha(b):return hashlib.sha256(b).hexdigest()
def need(b,m):
    if not b:raise RuntimeError(m)
def pinned(p,h):
    b=Path(p).read_bytes();need(sha(b)==h,'pin mismatch '+str(p));return b
src=pinned(P/'KernelRecipe.lean','13a3b32b1c87156229608a5e8cac2a33a2f85b8b87bec329f35b51cc71ab649a').decode()
phys=pinned(TASK/'Lean/DiophantineConsistency/MFWangTiles942PhysicalData.lean','208c3debcda84b159bc850feedc78628d36dd31bb8fd580598fa4d0988967f34').decode()
order=pinned(TASK/'Lean/DiophantineConsistency/MFWangTiles942PhysicalOrder.lean','39787941a0926b3553cee91ee900d8f6a7508509c2de41b6ba9332b338dcb8f8').decode()
table=pinned(TASK/'Lean/DiophantineConsistency/WangTiles942TableData.lean','0d2bf996f4e7e19acba82d5d3f1805a71c17cb1a9bcdc959e67453da14697a2c').decode()
need('def weightAt (p : Fin 942) : ℕ := Fin.cases (selectorWeight start) value p' in order,'weightAt mismatch')
need('selector_sum_reindex (fun pos weight => 2 * weight * r ^ (1005 - pos))' in src,'reindex theorem')
need('Nat.ofDigits_digits 256 _' in src and 'List.reverse_reverse _' in src and 'recipe_eq_kernel' in src,'decode proof')
chunks=re.findall(r'def chunk(\d+) : List \(ℕ × ℕ\) := (\[.*?\])',phys,re.S);need([x[0] for x in chunks]==[f'{i:02d}' for i in range(59)],'chunks')
section=phys.split('def rows : List (ℕ × ℕ) :=',1)[1].split('theorem rows_length',1)[0]
need(re.findall(r'chunk\d+',section)==[f'chunk{i:02d}' for i in range(59)],'concatenation')
rows=[]
for _,v in chunks:
 obj=ast.literal_eval(v);need(all(isinstance(a,int) and isinstance(b,int) for a,b in obj),'row type');rows.extend(obj)
need(len(rows)==941 and sorted(a for a,_ in rows)==list(range(1,942)),'row coverage')
need(all(a[1]>b[1] for a,b in zip(rows,rows[1:])),'weight order')
m=re.search(r'def start : Tile := ⟨(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩',table);need(m is not None,'start');w,n,e,s=map(int,m.groups())
start=1+(1<<10)*(1+w+(1<<8)*n+(1<<17)*e+(1<<25)*s);need(start==34876427265,'start weight')
controls=[(8,10,978),(9,18,960),(8,27,969),(9,35,942)]
terms=re.findall(r'∑ j : Fin (\d+), 2 \* 2 \^ \((\d+) \+ j.val\) \* r \^ \(1005 - \((\d+) \+ j.val\)\)',src);need([tuple(map(int,t)) for t in terms]==controls,'controls')
need('r ^ 18 + r ^ 1004 + r ^ 2020' in src and '∑ p : Fin 942, 2 * weightAt p * r ^ (1005 - p.val)' in src,'recipe formula')
# Independent Horner evaluation of the sparse radix coefficient vector.
coeff=[0]*2021
for k in (18,1004,2020):coeff[k]+=1
for pos,v in enumerate([start]+[w for _,w in rows]):coeff[1005-pos]+=2*v
for count,power,pos in controls:
 for j in range(count):coeff[1005-pos-j]+=1 << (power+j+1)
K=0
for v in reversed(coeff):K=(K<<47)+v
raw=K.to_bytes((K.bit_length()+7)//8,'big');need(len(raw)==11868 and K.bit_length()==94941 and sha(raw)=='64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7','computed bytes')
for rel,digest in [('research/current2011-ordinary67-94-candidate/polynomial.json','d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb'),('research/fourteen-normalized-product106/polynomial.json','0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1')]:
 gp=TASK/rel;g=json.loads(pinned(gp,digest));bind=g['coefficient_binding'];meta=bind['ports']['K0'];z=(gp.parent/bind['path']/meta['file']).read_bytes();need(sha(z)==meta['gzip_sha256'] and gzip.decompress(z)==raw,'payload '+rel)
r=pinned(P/'attempt02/state.json','f752ed2a04fc0ee2638d3687f2555abccf5796f49a10dccf015c05d1a5a0641d');d=json.loads(r)
need(d['status']=='PASS' and all(x['exit']==0 for x in d['runs']) and d['source_sha256']==sha(src.encode()),'producer state')
need(len(d['direct_guard'])==120,'guard count')
need(d['driver_sha256']==sha((P/'check-lean.py').read_bytes()),'runner hash')
need(d['preflight_before_sha256']==d['preflight_after_sha256']=='f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2','preflight pins')
need(d['runs'][0]['log_sha256']==sha((P/'attempt02/deps.txt').read_bytes()) and d['runs'][1]['log_sha256']==sha((P/'attempt02/compile.txt').read_bytes()),'run log hashes')
need(all('-M2800' in run['command'] and '180s' in run['command'] for run in d['runs']),'command limits')
expected_deps={'DiophantineConsistency.MFCurrentKernel2011','DiophantineConsistency.MFWangTiles942PhysicalOrder','Init'}
need(set(d['dependencies'])==expected_deps,'dependency set')
for name,entry in d['dependencies'].items():
    pp=Path(entry['path']);need(pp.is_file() and str(pp.resolve())==entry['realpath'] and sha(pp.read_bytes())==entry['sha256'],'dependency '+name)
actual=set((P/'attempt02/deps.txt').read_text().splitlines());need(actual=={entry['path'] for entry in d['dependencies'].values()},'dependency log')
need(sha(Path('/tmp/current2011-kernel-byte-recipe-check02-20261105/KernelRecipe.lean').read_bytes())==d['source_sha256'],'compiled source copy')
for path,rec in d['direct_guard'].items():
 p=Path(path)
 if rec is None:need(not os.path.lexists(p),'absent changed '+path)
 else:need(p.is_file() and str(p.resolve())==rec['realpath'] and sha(p.read_bytes())==rec['sha256'],'provider changed '+path)
log=pinned(P/'attempt02/compile.txt','5447f01430a0a9a19aa1a3c835d871e3dfb0e2061ff5e8e8bf06e3da764c6a24').decode()
reports=re.findall(r"'DiophantineConsistency.CurrentKernelBytes\.([^']+)' depends on axioms: \[([^\]]*)\]",log)
need([a for a,_ in reports]==['rawWord_recipe','recipe_eq_kernel','kernel_port','decode_kernel'],'axiom names')
need(all({q.strip() for q in b.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,b in reports),'axiom sets')
need(not any(x in log for x in ('warning:','error:','sorryAx')),'compiler diagnostic')
need(sha(Path('/tmp/current2011-kernel-byte-recipe-check02-20261105/KernelRecipe.olean').read_bytes())=='f973fcebb0440d40bc11ef28bb3f45e717599305d0246ec892e3d9a22ce5a073','object')
o=json.loads((P/'attempt02/outer-observation.json').read_text());need(o['actual_exit_code']==0 and o['session']==98472 and o['state_sha256']==sha(r),'outer exit')
t=json.loads((P/'bytes-terminal.json').read_text());obs=(P/'bytes-observation.json').read_bytes();need(t['actual_exit_code']==0 and t['observation_sha256']==sha(obs),'external exit')
need(json.loads(obs)['payloads'][0]['raw_sha256']==sha(raw),'observation mismatch')
print(json.dumps({'status':'PASS','checker_sha256':sha(Path(__file__).read_bytes()),'raw_sha256':sha(raw),'length':len(raw),'bits':K.bit_length(),'physical_rows':len(rows),'guards_rechecked':len(d['direct_guard']),'outer_session':o['session'],'scope':'Read-only source/receipt and independently reconstructed external bytes; no Lean replay or formal file-content statement.'},indent=2,sort_keys=True))
