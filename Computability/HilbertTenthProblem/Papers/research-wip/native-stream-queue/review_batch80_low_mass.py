#!/usr/bin/env python3
"""Portable pinned review of batch80 single-unit low-mass decidability packets."""
if not __debug__:raise RuntimeError('Run this audit without -O')
import argparse,contextlib,copy,csv,hashlib,io,itertools,json,math,os,re,stat,subprocess,sys,tempfile,types,zipfile
from collections import Counter
from fractions import Fraction
from pathlib import Path,PurePosixPath
COMMIT='4e270aa4648c5fd7e18626507531046715976535'
PINS={'four': {'archive': 'Four_Mass_Decidability_Package.zip', 'members': {'four-mass-bound/BINARY-EXPANDING-SHUTTLE.md': '75dda957b9f91a9383775aaf6dd8842d62d377b870bd8d1b9bb8082409d63eb1', 'four-mass-bound/EXPANDING-SHUTTLE.md': '078f3b6677a0b45ec075a170452b768d7f81f8c6e2bafc60d3fdbf9cb790a5ab', 'four-mass-bound/README.md': 'c642fed1339c7658caeff4c219d897861f322bc80bfd5d6f2c8ee76c95f2bee2', 'four-mass-bound/SHA256SUMS': 'cf3c1abaf574d86917584f67c556f7ed0aeaea2ba2206d1f37a103fa5656fcf7', 'four-mass-bound/SOURCE-PROVENANCE.md': 'ca648f77170d479e9ef18d292b76e4fc549c9445bad0c9e5533f18c2dd4cbf0a', 'four-mass-bound/binary-radius6-conservation-certificate.json': '6c99365818697ddd83bdbf529e17756fffaf2eacd55763b235919523b0041699', 'four-mass-bound/binary-shuttle-test-results.json': '5b4abe9c2b53013bbfb703c6069dfad90553fd6bdb5066b3e8ee157a81ad77e2', 'four-mass-bound/binary_exact.py': '1a94e2ac0a744fadf178c66163805e4d552f4e0997d45a860e53e8f91631d602', 'four-mass-bound/build.sh': 'dddcfca77fcc545bd75f8c2dc47c05f009b6d4004d41630d19f183c7b131951c', 'four-mass-bound/exact-boundary-results.json': '563c0a3cf2337614b85e1ea454f68ac9a085204be0a217849397212b4a24fdb6', 'four-mass-bound/figures/binary-four-particle-shuttle.csv': '1e7cc1488b57485aa6be03eed0d6665e5c88e54290ba65cf900de093755704f6', 'four-mass-bound/figures/binary-four-particle-shuttle.json': '8d31c9232690e6f4b72636d9c36690d9b9b4e29acf7b11f772bb3222f2c69104', 'four-mass-bound/figures/binary-four-particle-shuttle.pdf': 'df282dc977be73894bbec4a0f976252589c2529d908aa7f0c48d67b2ef5bd933', 'four-mass-bound/figures/binary-four-particle-shuttle.png': '8fedf2fa5f03e2ceb7d2eae29910a5f9cf01dcf11304d2e3689968186443e0da', 'four-mass-bound/figures/draw_binary_shuttle_trace.py': 'bd6cae1361ab1a3c8cb5f8b62f666ec1c02e50da74536501b2550696d8d4e723', 'four-mass-bound/finite-seed-section-lemma.md': '2c1ce0c7449ad15433da8206d226b71b5b97d190c98aeba1d42c2823857e06aa', 'four-mass-bound/four-mass-decidability.pdf': '0d1280e962e64e8e13486aaac0fae2498ac908f37feeeffba0d682df865f3f5e', 'four-mass-bound/four-mass-decidability.tex': '803bf0c4194bb9d0f1942e6ad3eb762c79d7a811bd785742ee63f0c46a775595', 'four-mass-bound/independent/BINARY-INDEPENDENT-AUDIT.md': '93dc24df9dfc972b415da4b4ca4aa451ae86b7c3336ca70550004937ce6c20db', 'four-mass-bound/independent/FINAL-REVIEW.md': 'a2d56ec0f9cbd52baf5bc4143ac1b145ef69b9b058b2da360151378933159804', 'four-mass-bound/independent/INDEPENDENT-AUDIT.md': '9fc260639a499cb9d0af4c5fd41ec560301e111211c91448476e82747da1471c', 'four-mass-bound/independent/audit-arithmetic-results.json': '1a03840c6297eb6ffb7ea66d164b693bfd8e2ff6135755e1ddaaa9d74f4eaa67', 'four-mass-bound/independent/audit_arithmetic.py': '26396fbf93584621f46f987442ec5dcc7907f8635a33cfc0ed99bab1bdfa743d', 'four-mass-bound/independent/audit_binary_shuttle.py': 'cbc0d1a18f5bfc9cdca3ae0189f071a0d0b073308d83977ffa8bac89ad6c9240', 'four-mass-bound/independent/binary-independent-audit-results.json': '6ec16b6784e183cd5f94c9a4e8730921b58d2366dd72b651fa4a9754d320ca70', 'four-mass-bound/independent/binary-rule-receipt.json': '630ee9a9639404fc151beafef6871feca74a277d286d497347070a5f8ac390c5', 'four-mass-bound/independent/check_binary_rule.py': 'fe1ae12aa0f1fd1e663d2af68fa30411c398f42539c58e4c80d94d053127135d', 'four-mass-bound/portable-replay-results.json': 'fe9c1fdbfe06824928f59ea7788a1344329c1085340ad7830ac6583b1c4f60fb', 'four-mass-bound/run-tests.sh': '6554743116e031cab22efa3f494be45257187b6ce0632725c4c748fc409bb0d7', 'four-mass-bound/shuttle-test-results.json': '62ab9322621ae0f1591ae86e21c7d3c6a0b14dd87ba09a2fb94d12a48ea18d81', 'four-mass-bound/test_binary_expanding_shuttle.py': '58eac70ab6246faae6b52c873da6183c4f10c3d4f766ff30f94a138e173ce49a', 'four-mass-bound/test_exact_boundaries.py': 'a0f3ce7ca925c3cb2915bb3bd439f600316733075465285a0c1938a4c4e35ab0', 'four-mass-bound/test_expanding_shuttle.py': 'b4c1fdfdc9fb284f841af1fd5eb3a34a62340fe970442e4f22591eafd34b5efc'}, 'sha256': '0bcc026a8ca7bd4745b82e6f9c2841073e5fb8c639970105690fc40803a780fe'}, 'single_original': {'archive': 'Single_Unit_Three_Mass_Decidability.zip', 'members': {'single-unit-three-mass/README.md': '3ed4a870e1e65d4e2c9ac62bbd023103d11547437913b8f1a534aa51d0c5c622', 'single-unit-three-mass/SHA256SUMS': 'b2dfa01ee3ac0d0e1db856b8d7d8f196c2d94d9bca2e71c284d9090515cf5020', 'single-unit-three-mass/SOURCE-PROVENANCE.md': 'cb39777ee83923080cf5ad66f7b1c3f68714954f47fc1e3a1bfb7252f6d2a644', 'single-unit-three-mass/build.sh': '482d94885f1e75204db77a9c0702fa9c1e71ca4a49ad815360db5fe3ae78e4ee', 'single-unit-three-mass/independent/AUDIT.md': '57579c812cb84e2ea73e8d2e3e9dce9e709995d5bf4b80baab409827736ecb67', 'single-unit-three-mass/independent/audit-results.json': '636f467e070273a7807c64d46b7775e591cd96c8711f9e3e6b930e8fe309c4f6', 'single-unit-three-mass/independent/audit_accelerator.py': '336bf75a1eab880ba3cd191b53bff1534fa951c46b43fa60087733b74fb48177', 'single-unit-three-mass/run-tests.sh': '8693262bd6c21531f8fd09530a5c859c450f650f49b7b3016e129de325bc081b', 'single-unit-three-mass/single-unit-mass-three.pdf': 'b210cdd6f91e30a258298f2fe224ad65ceeb1b22111c369c74b88a791486b398', 'single-unit-three-mass/single-unit-mass-three.tex': 'de38c287df1d74d0545e8025cfb333384b06ddcbc9f236a10a3b705296ba78b7', 'single-unit-three-mass/test-results.json': 'c0a19a459379e673ea98530f0e4d45ee07d81e3ef66f900a115115efe89dc124', 'single-unit-three-mass/test_single_unit_acceleration.py': '9df8027ca8dddc9fc3f3b73aed576bc3ea4e72d6104fac3833319b1e68a414d6'}, 'sha256': '25c0d2712b111ba9240fb11b23689b3eded14b059a5a793e33aa515f1c97f646'}, 'single_revised': {'archive': 'Single_Unit_Three_Mass_Decidability (1).zip', 'members': {'single-unit-three-mass/README.md': '04f58c0c3e8108c2ee2fc25be188a00b85d21d2a58080a75c391b6adfcf6166d', 'single-unit-three-mass/REVISION.md': '37c3124f0b91ccb8738b1bc767281672be0d971ac0d3d6b705e2632219a15a4a', 'single-unit-three-mass/SHA256SUMS': '9ebbf89b6d307117e352a94f7b5f5f08223e2be9a23b57dde04d9d7e30bf0cae', 'single-unit-three-mass/SOURCE-PROVENANCE.md': '0b4e4094959be1a719273a7142c1fe10e63209a1c8b57ca39b754c996d05cb3e', 'single-unit-three-mass/build.sh': '482d94885f1e75204db77a9c0702fa9c1e71ca4a49ad815360db5fe3ae78e4ee', 'single-unit-three-mass/independent/AUDIT.md': '57579c812cb84e2ea73e8d2e3e9dce9e709995d5bf4b80baab409827736ecb67', 'single-unit-three-mass/independent/audit-results.json': '636f467e070273a7807c64d46b7775e591cd96c8711f9e3e6b930e8fe309c4f6', 'single-unit-three-mass/independent/audit_accelerator.py': '336bf75a1eab880ba3cd191b53bff1534fa951c46b43fa60087733b74fb48177', 'single-unit-three-mass/run-tests.sh': '8693262bd6c21531f8fd09530a5c859c450f650f49b7b3016e129de325bc081b', 'single-unit-three-mass/single-unit-mass-three.pdf': '894542e181927e3ee531c9b0e9c4dc368c6f112bfa7ef3ff1a12c9f8e9e1ff25', 'single-unit-three-mass/single-unit-mass-three.tex': 'c02ff18f9ea5133884dc569bdce85aa7c53c9893e23f14efee56556fa45d5063', 'single-unit-three-mass/test-results.json': 'c0a19a459379e673ea98530f0e4d45ee07d81e3ef66f900a115115efe89dc124', 'single-unit-three-mass/test_single_unit_acceleration.py': '9df8027ca8dddc9fc3f3b73aed576bc3ea4e72d6104fac3833319b1e68a414d6'}, 'sha256': '299fef3508423dfe1fc88dc3473a39a40eac7cbfaf5d53c16dc26b9a3d119b12'}}

def need(b,m):
 if not b:raise ValueError(m)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def archive_bytes(tag,archives,repo):
 info=PINS[tag];path=archives/info['archive'] if archives else None
 if path is not None and path.is_file():data=path.read_bytes()
 else:
  need(repo is not None,'Supply --archives or --repo for pinned Git fallback')
  cmd=['git','show',COMMIT+':docs/incoming/'+info['archive']]
  r=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60);need(r.returncode==0,'Pinned archive fallback unavailable');data=r.stdout
 need(sha(data)==info['sha256'],'Changed archive '+info['archive']);return data

def extract(data,tag,out):
 expected=PINS[tag]['members'];seen=set();found={}
 with zipfile.ZipFile(io.BytesIO(data)) as z:
  for i in z.infolist():
   n=PurePosixPath(i.filename);need(not n.is_absolute() and '..' not in n.parts and '\\' not in i.filename and i.filename not in seen and not stat.S_ISLNK(i.external_attr>>16),'Unsafe/duplicate archive entry')
   seen.add(i.filename)
   if i.is_dir():continue
   b=z.read(i);found[i.filename]=sha(b);dest=out/n;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 need(exact(found,expected),'Complete archive member authentication');return out/next(iter(expected)).split('/')[0]

@contextlib.contextmanager
def module(path,pin,name):
 data=path.read_bytes();need(sha(data)==pin,'Module bytes changed before execution');old=sys.modules.get(name);present=name in sys.modules;m=types.ModuleType(name);m.__file__=str(path);sys.modules[name]=m
 try:exec(compile(data,str(path),'exec'),m.__dict__);yield m
 finally:
  if present:sys.modules[name]=old
  else:sys.modules.pop(name,None)

def revision(old,new):
 files_a={p.relative_to(old).as_posix():sha(p.read_bytes()) for p in old.rglob('*') if p.is_file()};files_b={p.relative_to(new).as_posix():sha(p.read_bytes()) for p in new.rglob('*') if p.is_file()}
 changed=[k for k in sorted(files_a.keys()|files_b.keys()) if files_a.get(k)!=files_b.get(k)]
 need(changed==['README.md','REVISION.md','SHA256SUMS','SOURCE-PROVENANCE.md','single-unit-mass-three.pdf','single-unit-mass-three.tex'],'Revision exact change inventory')
 a=(old/'single-unit-mass-three.tex').read_text();b=(new/'single-unit-mass-three.tex').read_text()
 start='\\section{Model and main result}';end='\\section{Primary sources and what remains unresolved}'
 need(a[a.index(start):a.index(end)]==b[b.index(start):b.index(end)],'All model/theorem/proof/quartic sections byte-identical')
 va=a[a.index('\\section{Executable checks and limits of validation}'):a.index('\\begin{thebibliography}')];vb=b[b.index('\\section{Executable checks and limits of validation}'):b.index('\\begin{thebibliography}')];need(va==vb,'Validation section unchanged')
 return dict(changed=changed,unchanged_common_members=len(files_a)-5,added_members=['REVISION.md'],mathematical_body_sha256=sha(a[a.index(start):a.index(end)].encode()),validation_section_sha256=sha(va.encode()),executables_and_saved_receipts_identical=True)

def manifest(root):
 count=0
 for line in (root/'SHA256SUMS').read_text().splitlines():
  if not line.strip():continue
  h,rel=line.split(None,1);rel=rel.lstrip('*');p=PurePosixPath(rel);need(not p.is_absolute() and '..' not in p.parts,'Safe supplied manifest path');need(sha((root/p).read_bytes())==h,'Supplied manifest mismatch '+rel);count+=1
 return count

def author_replays(four,single,original):
 schedule=[(four,['test_expanding_shuttle.py']),(four,['test_binary_expanding_shuttle.py']),(four,['independent/audit_arithmetic.py']),(four,['independent/audit_binary_shuttle.py']),(four,['independent/check_binary_rule.py']),(four,['test_exact_boundaries.py']),(four,['-O','test_exact_boundaries.py']),(single,['test_single_unit_acceleration.py']),(single,['independent/audit_accelerator.py'])]
 four_outputs=['shuttle-test-results.json','binary-shuttle-test-results.json','binary-radius6-conservation-certificate.json','independent/audit-arithmetic-results.json','independent/binary-independent-audit-results.json','independent/binary-rule-receipt.json','exact-boundary-results.json'];single_outputs=['test-results.json','independent/audit-results.json']
 before={(str(root),rel):(root/rel).read_bytes() for root,outputs in ((four,four_outputs),(single,single_outputs)) for rel in outputs}
 (four/'exact-boundary-results.json').unlink() # Force independent normal/optimized recording from scratch.
 commands=[]
 for root,args in schedule:
  r=subprocess.run([sys.executable,*args],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=300)
  need(r.returncode==0,'Author replay failed '+repr(args)+': '+r.stderr.decode(errors='replace')[-2000:]);commands.append(dict(package='four' if root==four else 'single_revised',arguments=args,exit_code=0))
 outputs={}
 for root,rels in ((four,four_outputs),(single,single_outputs)):
  for rel in rels:
   old=before[str(root),rel];fresh=(root/rel).read_bytes();need(exact(json.loads(old),json.loads(fresh)),'Exact typed author receipt mismatch '+rel)
   need(fresh==old,'Original deterministic export byte mismatch '+rel)
   key=('four/' if root==four else 'single/')+rel;outputs[key]=dict(sha256=sha(fresh),result=json.loads(fresh))
   if root==single:need(fresh==(original/rel).read_bytes(),'Same replay also authenticates original identical-code receipt')
 return dict(commands=commands,byte_identical_exports=outputs,scope='Nine meaningful author Python invocations; identical original/revised single-unit sources executed once. TeX/PDF and optional matplotlib image rebuilds are not run.')

RULES=(((0,1),(1,2)),((0,2),(-1,1)),((0,1,3),(-1,1,4)),((0,2,4),(0,3,4)))
def local(s,x):
 value=int(x in s);edits=[]
 for before,after in RULES:
  for off in set(before)^set(after):
   origin=x-off;region=range(origin-2,origin+max(before)+3)
   if s.intersection(region)=={origin+j for j in before}:edits.append(int(off in after)-int(off in before))
 need(len(edits)<=1,'Disjoint exact-pattern edits');return value+sum(edits)
def literal_step(s):
 return frozenset(x for x in {i+j for i in s for j in (-1,0,1)} if local(s,x))
def closed(d,t):
 k=(math.isqrt((2*d-11)**2+4*t)-(2*d-11))//2;D=d+k;s=t-k*k-(2*d-11)*k
 need(0<=s<2*D-10,'Exact cycle index')
 return frozenset((0,3+s,4+s,D) if s<=D-6 else (0,2*D-9-s,2*D-7-s,D+1)),k,s

def binary_checks(root):
 c=Counter();certificate=json.loads((root/'binary-radius6-conservation-certificate.json').read_text());table=[int(x) for x in certificate['rule_bits_indexed_by_window']];pot=certificate['potential_by_vertex']
 pin=PINS['four']['members']['four-mass-bound/binary_exact.py']
 with module(root/'binary_exact.py',pin,'_batch80_binary_exact') as m:
  for word in range(8192):
   s={i-6 for i in range(13) if word>>i&1};need(local(s,0)==table[word]==int(0 in m.step(s)),'Independent exact guarded rule window');need(table[word]-((word>>6)&1)==pot[word>>1]-pot[word&4095],'Every conservation potential edge');c['literal_rule_windows']+=1;c['potential_edges']+=1
  for d in range(7,16):
   current=frozenset((0,3,4,d));end=12*12+(2*d-11)*12
   for t in range(end+1):
    expected,k,s=closed(d,t);need(current==expected and (current.intersection(range(5))==frozenset((0,3,4)))==(s==0),'All-phase closed orbit and hit exclusivity');need(current==m.step(closed(d,t-1)[0]) if t else True,'Actual strict helper on orbit');c['complete_orbit_states']+=1;current=literal_step(current)
  for d,k in itertools.product((7,8,31,10**50+7),(0,1,5,10**70)):
   D=d+k;T=k*k+(2*d-11)*k
   for s in sorted({0,1,D-7,D-6,D-5,2*D-12,2*D-11}):
    if 0<=s<2*D-10:
     a,_,_=closed(d,T+s);b,_,_=closed(d,T+s+1);need(literal_step(a)==b==m.step(a),'Huge boundary formula');c['huge_boundary_transitions']+=1
  need(literal_step({0,1,4,6})==literal_step({1,2,3,5})==frozenset((1,2,3,5)),'Noninjectivity is literal, not reversible')
  for x in range(5):
   for den in range(2,10):
    for num in range(1,5*den):
     k=Fraction(num,den);t=k*k+(2*x+3)*k;need(t.denominator!=1 or k.denominator==1,'Monic rational-root domain census');c['rational_root_cases']+=1
  for x,k in itertools.product((0,1,10**80),(0,1,10**70)):
   t=k*(k+2*x+3);need(m.hit_time(x,k)==t and m.quartic(x,t,k)==0 and m.quartic(x,t+1,k)==1,'Huge exact timing source');c['huge_timing_cases']+=1
  def reject(fn):
   try:fn()
   except (ValueError,TypeError):c['malformed_public_rejections']+=1;return
   raise ValueError('Malformed public helper accepted')
  for fn,args in ((m.hit_time,[0,0]),(m.quartic,[0,0,0])):
   for i in range(len(args)):
    for v in (True,False,1.0,Fraction(1),-1,None):
     a=list(args);a[i]=v;reject(lambda a=a,fn=fn:fn(*a))
  for v in ([True],[1.0],[Fraction(1)],[0,0],None,{'a':1}):reject(lambda v=v:m.step(v))
  for key in ('radius','verified_edges','verified_vertices'):
   for v in (True,1.0,-1):
    z=copy.deepcopy(certificate);z[key]=v;reject(lambda z=z:m.verify_certificate(z))
  z=copy.deepcopy(certificate);snap=m.validate_certificate(z);z['potential_by_vertex'][0]+=1;need(snap.potential[0]==pot[0],'Deep immutable certificate snapshot');reject(lambda:m.verify_certificate(z));c['immutable_snapshot_checks']+=1
 # Independently verify exact plotted data; do not regenerate nondeterministic image metadata.
 data=json.loads((root/'figures/binary-four-particle-shuttle.json').read_text());need(data['d']==9 and data['return_times']==[0,8,18,30,44],'Figure geometry')
 for row in data['trace']:
  s,k,phase=closed(9,row['t']);need(sorted(s)==row['occupied_sites'] and max(s)==row['rightmost_site'] and row['return_index']==(k if phase==0 else None),'Every figure state');c['figure_states']+=1
 rows=list(csv.reader((root/'figures/binary-four-particle-shuttle.csv').read_text().splitlines()))
 for row,expected in zip(rows[1:],data['trace']):need([str(expected['t']),*map(str,expected['occupied_sites']),str(expected['rightmost_site']),'' if expected['return_index']is None else str(expected['return_index'])]==row,'CSV exact trace export')
 need(len(rows)==len(data['trace'])+1,'No extra or omitted plot rows')
 # Literal paid six-gate circuit with free x,t and one natural witness k.
 gates=[('twox','+','x','x'),('offset','+','twox',3),('sum','+','k','offset'),('prod','*','k','sum'),('residual','-','prod','t'),('output','*','residual','residual')]
 for x,t,k in itertools.product(range(4),range(15),range(8)):
  e=dict(x=x,t=t,k=k)
  for n,o,a,b in gates:
   a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a*b if o=='*' else a+b if o=='+' else a-b
  need(e['output']==(k*k+(2*x+3)*k-t)**2,'Full six-operation quartic source');c['full_quartic_source_identities']+=1
 return dict(counts=dict(c),quartic_complete_source=gates,ledger=dict(operations=6,M=2,A=4,natural_witnesses=1,degree=4),domain_boundaries=dict(nonnegative_real_false_hit=dict(x=0,t=1,witness='(sqrt(13)-3)/2'),signed_second_root='-k-(2*x+3)'),scope='Exact local conservation certificate plus explicit orbit/arithmetic proofs; finite cases do not certify arbitrary four-mass CA theorem.')

def single_checks(root):
 c=Counter();pin=PINS['single_revised']['members']['single-unit-three-mass/test_single_unit_acceleration.py']
 with module(root/'test_single_unit_acceleration.py',pin,'_batch80_single_accelerator') as m:
  for A,D,lo,hi in itertools.product(range(-6,7),range(-4,5),range(-6,7),range(-6,7)):
   expected=next((n for n in range(32) if lo<=A+n*D<=hi),None);need(m.first_linear_hit(A,D,lo,hi)==expected,'Independent signed first-hit arithmetic');c['linear_first_hit_cases']+=1
  # Independently evaluate the complete elementary tables, including frame translation.
  for rule in (170,184,204,226,240):
   ca=m.eca_ca(rule)
   def direct(s):
    candidates={y for x in s for y in (x-1,x,x+1)};out=set()
    for x in candidates:
     bits=4*(x-1 in s)+2*(x in s)+(x+1 in s)
     if rule>>bits&1:out.add(x-ca.delta)
    return out
   cases=[set(xs) for size in range(4) for xs in itertools.combinations(range(-3,5),size)]+[{-10**40,0,10**40},{0,1,10**40}]
   for s in cases:
    a=m.Accelerator(ca,dict.fromkeys(s,'u'));cur=s
    for t in range(24):need(a.at(t)==dict.fromkeys(cur,'u'),'Independent full elementary CA orbit');cur=direct(cur);c['independent_eca_orbit_states']+=1
   c['eca_initial_configurations']+=len(cases)
  # Cases omitted from the primary sample list but covered by the mathematical proof:
  # no unit label, radius zero, periodic heavy labels, and huge exact time.
  ca=m.CA('no-unit-radius-zero',0,{'a':2,'b':2,'c':3,'d':3},lambda c:{x:{'a':'b','b':'a','c':'d','d':'c'}[v] for x,v in c.items()})
  for name in ('a','b','c','d'):
   a=m.Accelerator(ca,{-10**50:name})
   for t in (0,1,2,10**80,10**80+1):
    wanted=name if t%2==0 else {'a':'b','b':'a','c':'d','d':'c'}[name];need(a.at(t)=={-10**50:wanted},'No-unit finite-state walker boundary');c['no_unit_radius_zero_cases']+=1
 return dict(counts=dict(c),scope='Independent actual ECA transitions and signed acceleration arithmetic, plus proof-covered no-unit/radius-zero examples. Sample accelerator remains an internal u-label harness, not an arbitrary-rule-to-Presburger compiler.')

def verify(archives=None,repo=None):
 with tempfile.TemporaryDirectory(prefix='review-batch80-low-mass-') as directory:
  base=Path(directory);roots={};inputs={}
  for tag in PINS:
   data=archive_bytes(tag,archives,repo);roots[tag]=extract(data,tag,base/tag);inputs[tag]=dict(archive=PINS[tag]['archive'],sha256=sha(data),members=PINS[tag]['members'],manifest_entries=manifest(roots[tag]))
  revised=revision(roots['single_original'],roots['single_revised'])
  replay=author_replays(roots['four'],roots['single_revised'],roots['single_original'])
  binary=binary_checks(roots['four']);single=single_checks(roots['single_revised'])
 return json.loads(json.dumps(dict(status='PASS_BATCH80_LOW_MASS_REVIEW',source_commit=COMMIT,inputs=inputs,revision=revised,author_replay=replay,independent_binary=binary,independent_single=single,
  proof_scope='Full mathematical read of original/revised single-unit theorem and four-mass argument including finite seed thresholds and anchored cutoff. Exact theorem reasoning remains distinct from bounded computation. No general rule-to-formula/section compiler, universal arithmetic improvement or full historical literature survey claimed.')))

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--archives',type=Path);p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.archives,a.repo)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Typed full saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],revision=r['revision'],author_invocations=len(r['author_replay']['commands']),binary=r['independent_binary']['counts'],single=r['independent_single']['counts']),indent=2))
