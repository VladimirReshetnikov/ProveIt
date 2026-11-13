#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-full-coefficients-blocks-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e9f0aab6eff804e10dd6da682b4d53845a6803296f25603603f77033472a6146' and sha(p/'source-manifest.json')=='49b621909df8d072506193b59279e49eb41cb256f5c79082a9ec2d22ac8f57bf'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KFullCoefficients.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KFullCoefficients' and e['imports']==['DiophantineConsistency.Sign17KControlBlockSum'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('def coefficients : Fin 986 → ℕ := Fin.append','(fun i : Fin 942 => 2 * Sign17KWeightUnion942.weights i)','Sign17KControlBlocks.literal','theorem coefficient_sum (r : ℕ)','Fin.sum_univ_add (a := 942) (b := 44)','r ^ (1005 - (942 + i.val))','rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020','Sign17KRankedRawWord.rawWord_ranked, Sign17KControlBlockSum.controls_as_sum, coefficient_sum','theorem K_coefficients : K = radix ^ 18 + radix ^ 1004 + radix ^ 2020'):assert t in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-control-block-sum-retry-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'Fin986 in-Lean tile/control recipe with 3 sentinels separate; external array/file binding unproved'},indent=2))
