#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-control-blocks-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='dab583eab6a91a06b291f2ce868c990c203ccc8c7929dfd8d0cbe5f9b4d9cfe2' and sha(p/'source-manifest.json')=='cefb22a41837bf98f0c4e65824d95e78001ff49fb48f04917e91a723d3825a9f'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KControlBlocks.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KControlBlocks' and e['imports']==['DiophantineConsistency.Sign17KRankedRawWord'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
m=re.search(r'^def literal : Fin 44 → ℕ := !\[([^]]+)\]',s,re.M);assert m;v=[int(x) for x in m.group(1).split(',')];assert len(v)==44
independent=[0]*44
for length,weight,pos in ((8,10,978),(9,18,960),(8,27,969),(9,35,942)):
 for j in range(length):independent[pos+j-942]+=2**(weight+j+1)
coeff=root/'research/padding-staircase-independent/coefficients.json';assert sha(coeff)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93' and v==independent==json.loads(coeff.read_text())[942:986]
for t in ('def south (i : Fin 9) : ℕ := 2 * 2 ^ (35 + i.val)','def gap9 (_ : Fin 9) : ℕ := 0','def north (i : Fin 9) : ℕ := 2 * 2 ^ (18 + i.val)','def east (i : Fin 8) : ℕ := 2 * 2 ^ (27 + i.val)','def gap1 (_ : Fin 1) : ℕ := 0','def west (i : Fin 8) : ℕ := 2 * 2 ^ (10 + i.val)','Fin.append south (Fin.append gap9','Fin.append north (Fin.append east (Fin.append gap1 west))','theorem symbolic_eq_literal (i : Fin 44) : symbolic i = literal i'):assert t in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-control-coefficients-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-ranked-rawword-retry-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','coefficients':44,'control_terms':34,'scope':'symbolic control blocks = literal vector, external slice match Python only'},indent=2))
