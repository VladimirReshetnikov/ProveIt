"""Portable Python 3 standard-library verification; never imports upstream code.
INTERNAL: run only in a disposable worktree; use verify_package.py publicly.
All finite checks supplement, rather than replace, the included proofs.
"""
from pathlib import Path
import json,gzip,hashlib,random,subprocess,sys,time,math
ROOT=Path(__file__).resolve().parent
if not __debug__ or sys.flags.optimize:
 raise SystemExit('ERROR: verification requires unoptimized Python; remove -O and PYTHONOPTIMIZE.')
START=time.monotonic()
def digest(b):return hashlib.sha256(b).hexdigest()
manifest=ROOT/'SHA256SUMS.txt'
if not manifest.is_file():raise SystemExit('ERROR: SHA256SUMS.txt is required.')
if manifest.exists():
 for line in manifest.read_text().splitlines():
  expected,path=line.split('  ',1)
  assert digest((ROOT/path).read_bytes())==expected,('Manifest mismatch',path)
 print('PASS: release SHA-256 manifest',flush=True)
pins=json.loads((ROOT/'review/SOURCE_PINS.json').read_text())
for row in pins['files']:
 raw=(ROOT/'review'/row['local_path']).read_bytes()
 assert digest(raw)==row['sha256'] and len(raw)==row['bytes']
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==row['git_blob_sha']
print('PASS:',len(pins['files']),'inert pinned source files, SHA-256 and Git blob SHA',flush=True)
binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
values={};payloads=[]
for row in binding['files']:
 p=ROOT/row['path'];gz=Path(str(p)+'.gz');compressed=gz.read_bytes()
 assert digest(compressed)==row['gzip_sha256']
 raw=gzip.decompress(compressed)
 assert len(raw)==row['bytes'] and digest(raw)==row['sha256']
 value=int.from_bytes(raw,'little');assert value.bit_length()==row['bit_length'] and raw[-1]
 p.write_bytes(raw);values[row['name']]=value
 payloads.append(dict(name=row['name'],bytes=len(raw),sha256=digest(raw)))
B=values['beta']+1;MF_native=values['MF_source']-B+1
assert B==1<<9765625 and values['MC'].bit_count()+MF_native.bit_count()==9765625
assert MF_native.bit_count()==989 and values['MC']%4==2 and MF_native%8==4
DC,DR=values['K'] & (B-1),values['K'] >> 9765625
assert (2*DC-DR)%5==4
print('PASS: four actual compact coefficients, populations and congruences',flush=True)
forms=json.loads((ROOT/'FINAL_FORMS.json').read_text())
def evaluate(j,env,p=None):
 env=env.copy()
 for n,op,a,b in j['source']:
  a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
  x=a+b if op=='+' else a-b if op=='-' else a*b;env[n]=x%p if p else x
 return env

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def polyop(op,a,b,p):
 if op=='*':
  n=len(a)+len(b)-1
  assert min(len(a),len(b))*(p-1)**2 < 2**64
  x=int.from_bytes(b''.join(v.to_bytes(8,'little') for v in a),'little')
  y=int.from_bytes(b''.join(v.to_bytes(8,'little') for v in b),'little')
  z=(x*y).to_bytes(8*n,'little')
  return trim([int.from_bytes(z[i:i+8],'little')%p for i in range(0,len(z),8)])
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]=x
 for i,x in enumerate(b):c[i]=(c[i]+(x if op=='+' else -x))%p
 return trim(c)

def degrees(j,p,seed):
 rng=random.Random(seed)
 e={n:[rng.randrange(1,p),rng.randrange(1,p)] for n in j['witnesses']}
 # Actual coefficient tuple reduced modulo p, not free placeholder constants.
 e.update({n:[values[binding['port_aliases'][n]]%p] for n in j['fixed_numerals']})
 for n,op,a,b in j['source']:
  a=e[a] if isinstance(a,str) else [a%p];b=e[b] if isinstance(b,str) else [b%p]
  e[n]=polyop(op,a,b,p)
 if 'output' in j:return [len(e[j['output']])-1]
 return [len(polyop('-',e[a] if isinstance(a,str) else [a%p],e[b] if isinstance(b,str) else [b%p],p))-1 for a,b in j['comparisons']]

def ringmul(x,y,A,G,p):
 z=[0]*4
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i^j]=(z[i^j]+a*b*(A if i&j&1 else 1)*(G if i&j&2 else 1))%p
 return z

def norm_check(j,scaled):
 rng=random.Random(20261022);p=1000000007
 for case in range(100):
  e={n:rng.randrange(1,100) for n in j['witnesses']}
  e.update({n:values[binding['port_aliases'][n]]%p for n in j['fixed_numerals']})
  e=evaluate(j,e,p);A,G=e['Afirst'],e['Gmain'];d=1 if scaled else e['daux']
  ee=e['eraux'] if scaled else e['eaux'];BB=e['Braux'] if scaled else e['Baux'];H=e['H']
  prod=[1,0,0,0]
  for sr,ss in [(1,1),(1,-1),(-1,1),(-1,-1)]:
   W=[e['Zlinear'],-sr*e['uweight'],-ss*e['Kweight'],0]
   inn=[d*x%p for x in ringmul(W,W,A,G,p)];inn[0]=(inn[0]-H*H*ee)%p
   f=ringmul(inn,inn,A,G,p);f[0]=(f[0]-H**4*BB*BB*e['Dstrong'])%p
   prod=ringmul(prod,f,A,G,p)
  assert prod==[e['Res12'],0,0,0]
 return 100

results=[]
for info in forms:
 p=ROOT/info['path'];assert digest(p.read_bytes())==info['sha256'];j=json.loads(p.read_text())
 known=set(j['witnesses']+j['fixed_numerals']);defs={}
 for n,op,a,b in j['source']:
  assert n not in known and op in '+-*'
  assert all(isinstance(x,int) or x in known for x in (a,b));known.add(n);defs[n]=[a,b]
 live=set();todo=[j['output']] if 'output' in j else [v for c in j['comparisons'] for v in c if isinstance(v,str)]
 while todo:
  n=todo.pop()
  if not isinstance(n,str) or n in live:continue
  live.add(n);todo.extend(defs.get(n,[]))
 assert known==live
 ledger=j['ledger'];assert len(j['source'])==ledger['operations']
 assert sum(op=='*' for _,op,_,_ in j['source'])==ledger['multiplications']
 observed=[degrees(j,p,seed) for p,seed in [(65521,1941),(65519,1942)]]
 expected=[j['exact_degree']] if 'output' in j else j['residual_exact_degrees']
 assert observed==[expected,expected],(info['path'],expected,observed)
 r=dict(path=info['path'],variables=len(j['witnesses']),operations=len(j['source']),degree_diagnostics=observed,actual_coefficient_residues=True,all_gates_and_ports_live=True)
 if info['path'].startswith('roots/') and 'output' in j:r['independent_four_factor_evaluations']=norm_check(j,'scaled_y' in info['path'])
 results.append(r)
 print('PASS:',info['path'],flush=True)
# Run only explicitly identified newly authored checkers. No upstream program runs.
checks=['audit/audit_wang943_independent.py','audit/audit_wang943_compact_independent.py',
        'compiler/check_wang_helices.py','audit/audit_compiler_port_bindings.py',
        'audit/check_final_math_independent.py','integers/verify_integer26.py',
        'integers/verify_integer26_unscaled.py','integers/verify_integer27.py','integers/verify_integer28.py','integers/verify_integer28_amalgam.py']
logs=ROOT/'verification_logs';logs.mkdir(exist_ok=True)
for name in checks:
 result=subprocess.run([sys.executable,'-B',str(ROOT/name)],cwd=ROOT,text=True,capture_output=True)
 (logs/(Path(name).stem+'.txt')).write_text(result.stdout+result.stderr)
 assert result.returncode==0,(name,result.stdout[-2000:],result.stderr[-2000:])
 print('PASS:',name,flush=True)
# Verify the printed primary SLP matches every gate in the authoritative JSON.
tex=(ROOT/'report/twelve_variable_con_zfc.tex').read_text()
for row in binding['files']:assert row['sha256'] in tex,('Printed coefficient hash mismatch',row['name'])
assert '192 gates: 117 multiplications and 75 additions/subtractions' in tex
assert r'W_b=2\bigl((Si)v^2+b\bigr)' in tex
j=json.loads((ROOT/'roots/root12_saturated_product.json').read_text());printed=(ROOT/'report/primary_circuit.tex').read_text()
def esc(x):return str(x).replace('_',r'\_')
for k,(n,op,a,b) in enumerate(j['source'],1):
 expected=f'{k} & \\texttt{{{esc(n)}}} & \\texttt{{{esc(a)}}} & ${op}$ & \\texttt{{{esc(b)}}}\\\\'
 assert expected in printed,(k,n)
receipt=dict(status='PASS',scope='Finite reproducible checks only; inherited theorems and unbounded proofs remain necessary.',pinned_source_files=len(pins['files']),coefficient_payloads=payloads,circuits=results,independent_checkers=checks,primary_printed_slp_matches=True,elapsed_seconds=round(time.monotonic()-START,2))
(ROOT/'VERIFICATION_RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: complete portable verification; see VERIFICATION_RESULT.json',flush=True)
