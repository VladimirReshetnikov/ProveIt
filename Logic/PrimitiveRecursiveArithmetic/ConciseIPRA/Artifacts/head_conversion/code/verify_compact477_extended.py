"""Check the new opener's alias lemma and ordinary computation families."""
from pathlib import Path
import ast, concurrent.futures, copy, hashlib, io, json, random, subprocess, sys, tokenize
ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT/'reference/incumbent_bytes478.py'
CAND = ROOT/'code/compact477.py'
MISSING = object()

def opener(a, t=MISSING, d=0, k=0, new=False):
    if type(a) is list:
        return [opener(b,t,d+5-len(a),k,new) for b in a]
    if type(a) is not int:
        raise ValueError('missing or ill-typed image')
    if k <= a < d:
        return a
    if new:
        return (d%2)*opener(t,d=3,k=k,new=True)
    return d%2 and opener(t,d=3,k=k)

def erase_empty(a):
    return [erase_empty(b) for b in a] if type(a) is list and a else 0 if type(a) is list else a

def attempt(*args, **kwargs):
    try: return True, opener(*args, **kwargs)
    except (TypeError, ValueError, RecursionError): return False, None

rng = random.Random(20261112)
def raw(depth=0):
    if depth >= 3 or rng.randrange(3)==0:
        return rng.randrange(-5,13)
    return [raw(depth+1) for _ in range(rng.randrange(8))]

def numerical_zero_alias_check():
    checked=0; successful=0; different=0
    for n in range(5000):
        a,t=raw(),raw();d=rng.randrange(-6,12);k=rng.randrange(-4,1)
        oknew,new=attempt(a,t,d,k,new=True)
        okold,old=attempt(a,t,d,k,new=False)
        checked+=1
        if oknew:
            successful+=1
            if not okold or erase_empty(new)!=erase_empty(old):
                raise AssertionError((a,t,d,k,okold,old,new))
            different+=new!=old
    return dict(calls=checked,new_successes=successful,raw_differences=different,violations=0)

def numeral(n):
    a=0
    for _ in range(n): a=[a]
    return a

# All templates below are canonical one-hole numerical templates.
# Their state slot is 3 at the numerical root; each constructor adds its
# established dummy/bound slots before the hole is encountered.
TEMPLATES = [0, numeral(1), numeral(2), 3, [7], [[11]],
             [0,5,3], [5,0,3], [[9],0,3], [0,5,[7]]]
SOURCES = [0,numeral(1),numeral(2),[0,0,0]]
SEEDS = [numeral(1),numeral(2),[0,0,0]]
FIX = ROOT/'tests/compact477/generated'; FIX.mkdir(parents=True,exist_ok=True)
jobs=[]
for sn,s in enumerate(SOURCES):
 for un,u in enumerate(SEEDS):
  for tn,t in enumerate(TEMPLATES):
   recursive=[s,u,t]
   endpoint=opener(t,recursive,3) if s else u
   goal=[[s and [s],u,t],endpoint]
   packet=[[],s,u,t]
   base_packet=[0,s,u,t]
   title=f'compute_s{sn}_u{un}_t{tn}'
   for bad in (False,True):
    a=copy.deepcopy(goal)
    if bad:a[1]=[a[1]]
    suffix='_wrong_endpoint' if bad else ''
    data=[packet,[a,0]];base_data=[base_packet,[a,0]]
    filename=title+suffix+'.json'
    (FIX/filename).write_text(json.dumps(data,separators=(',',':'))+'\n')
    jobs.append((filename,not bad,base_data,data))

def run(job):
    name,expected,old,new=job;results=[]
    for program,data in ((BASE,old),(CAND,new)):
        for opt in (False,True):
            cmd=[sys.executable,'-I','-S','-B']+(['-O'] if opt else [])+[str(program)]
            proc=subprocess.run(cmd,input=json.dumps(data).encode(),capture_output=True,timeout=10)
            accepted=proc.returncode==0 and proc.stdout==b'ACCEPT\n'
            results.append({'program':program.name,'optimized':opt,'accepted':accepted,'passed':accepted==expected})
    return {'fixture':name,'expected':expected,'results':results}

with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    results=list(pool.map(run,jobs))
failures=[x for x in results if any(not y['passed'] for y in x['results'])]
report={'python':sys.version,'opener_alias_check':numerical_zero_alias_check(),
        'generated_fixture_count':len(jobs),'generated_process_executions':4*len(jobs),
        'failures':failures,'results':results}
(ROOT/'evidence/compact477_extended.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
if failures:raise SystemExit(1)
