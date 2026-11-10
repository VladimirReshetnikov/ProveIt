#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-control-coefficients-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='07bff1f1d70cdad5352d96d1d07581660168f69f8772c1a238c414fd71dd2271' and sha(p/'source-manifest.json')=='db7b6de832528d274ed4ed37b37e7dd9d33b1a29dbbe50bcc81fc7e34bf01ad4'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KControlCoefficients.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KControlCoefficients' and e['imports']==['DiophantineConsistency.Sign17KRankedRawWord'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
m=re.search(r'^def coefficients : Fin 44 → ℕ := !\[([^]]+)\]',s,re.M);assert m;v=[int(x) for x in m.group(1).split(',')];assert len(v)==44
independent=[0]*44
for length,weight,pos in ((8,10,978),(9,18,960),(8,27,969),(9,35,942)):
 for j in range(length):independent[pos+j-942]+=2**(weight+j+1)
coeff=root/'research/padding-staircase-independent/coefficients.json';assert sha(coeff)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93' and v==independent==json.loads(coeff.read_text())[942:986]
for t in ('theorem controls_as_sum (r : ℕ)','Sign17KRankedRawWord.controls r','∑ i : Fin 44, coefficients i * r ^ (1005 - (942 + i.val))','rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020','Sign17KRankedRawWord.rawWord_ranked, controls_as_sum'):assert t in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-ranked-rawword-retry-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','coefficients':44,'control_terms':34,'scope':'symbolic controls vector and rawWord split; external slice match is Python only, sentinels separate'},indent=2))
