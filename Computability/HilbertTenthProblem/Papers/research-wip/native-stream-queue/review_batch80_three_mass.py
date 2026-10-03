#!/usr/bin/env python3
"""Pinned independent review of the two batch80 three-mass packages.

All sources are authenticated before execution. Optional complete author replays
run against isolated copies. No archive or repository file is changed.
"""
if not __debug__:raise RuntimeError('Use Python without -O for inherited test assertions')
import argparse,contextlib,copy,hashlib,itertools,json,os,random,shutil,stat,subprocess,sys,tempfile,types,zipfile
from collections import Counter,defaultdict
from fractions import Fraction
from pathlib import Path,PurePosixPath
PINS={'Three_Mass_Reversible_Computation.zip': {'sha256': 'fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de', 'prefix': 'three-mass-release/', 'members': {'README.md': '0abb90d9af2419e58fc3e67f86672e8076e7293dfd41cb0fe2477722cc1f415d', 'SHA256SUMS': 'c9efd37d0c489d9ca3613a89846b2282b0b837558696bd161f7b85b55da0b581', 'SOURCE_PROVENANCE.md': 'f19fd356f6469e6954f29a40bcd36363979b7f09fae900173d67cd856a6c13b1', 'build.sh': '318764bcb642652d63d1794afcfe43e8f00d34e257f82fb9484758c7388f6996', 'code/certificate.py': 'fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8', 'code/checker.py': '9fc3879eb24f4b4d9d2e1c8ebc0c123510c04141bd754547d191ceef28815c66', 'code/export_examples.py': '5a09fc290664e6a9222e4448b7a4ca2fb296faed6bffc21bd9a88262b9920036', 'code/legacy/certificate.py': 'bfc7588058b68ce773a91af8ca0730647cb3c9cb1821dda5928a534aa33d97ed', 'code/legacy/checker.py': '9068dd7a87c2e5ee001b957ea2bc0483b625fe155d14cf610261c8a4e06f0165', 'code/radius_one.py': '99cae9e9b3d1ceac7b34392e2fe32772daaa88394700ea0c820aa72d3fe5433c', 'code/spatial_radius_one.py': '6842cecac0ce20e62d1b0ef18347e52d1db574e11c2d71c3f22a11abf6ae149b', 'code/test_certificate_hardening.py': '465a1e34e6f463e3394265b21adeef1616f4db53e057ab26ec875fc84b254de7', 'code/test_certificates.py': '6b05b1793e58c0ac0f9cb3d8a1dcbf1b3ab3f1f76b64fe5f9b43fb99fc65b140', 'code/test_certificates_independent.py': 'c9ac802aaf016eb2f635e48a7694ce0b3bb5c56b3ca102891e018341de085639', 'code/test_checker_mutations.py': '168a7b6300ed9c0f576ab9200604de184a6fb4300458343e3086d3bd2ee4aac2', 'code/test_clock_scale_independent.py': '74b514a24877721e0f8a7b9fe5d9010f884f2ffb4e7b38bfd5d58003fa4fdf5c', 'code/test_literal_exports.py': '1aaf61505e9c4bf5e6846cb7faf8ee93ac92fc9fae2f0ed7d226048d4c1929b3', 'code/test_radius_one.py': '757e1635d134f558cc7038784b3255f48155d3d48d5bb9a775722b3986ca6ea9', 'code/test_radius_one_boundaries.py': '8046f345c39c62a2c74f31733474ae35f144be2d19b99695e538dc99f378b1e8', 'code/test_size_ledger.py': '956c8792bc9a7e5ac019fba34e8407ae5cc82d577a4f190bf5186164a4c2a59e', 'code/test_spatial_radius_one.py': '5c64f142799d748fcd45a888c317291fd837c9763d363ca202cd639ca0bae223', 'code/test_three_mass_independent.py': '915f8cd057aabb14172c65fc0f1b0e51822b851d01306b2539f84ea2074b6094', 'code/test_two_mass_arithmetic.py': '8d086a7c5d7efea1b56a20df87cf55acad4504fca4825b5c6ab689ac6878f879', 'code/three_mass_collision_generator.py': '14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52', 'examples/chain_certificate.json': '99ae412178ff228a1afab7e1fc208096dd0effa32ecd773608e4c3452173e52f', 'examples/chain_check.json': '33705a299d3c1169eacebdd0a0bdbd7e1cb9fc85ea4b33d3cd462c6ecd988bfd', 'examples/chain_request.json': '7ae76fdc8a33013d77d09a8e0a325d93369021636499259557802500cb067ec2', 'examples/chain_witness.json': '39e57a9e55b636c4df0595d96896aa8f3c6e1bfba2d962d111bff0528d487601', 'examples/cycle_rule.json': 'cb3b345d17a0961d9916c0434cca88631ac7be86adfce1e798641adebf49c962', 'examples/merge_rule.json': 'c348e42c22ce0be78bb07b0d7b360a405c4d6fb1d7d5c85aad328a1790eb81e9', 'examples/mixed_certificate.json': 'f7210e16c891db997672077ff34b6df4836d98b671d9ab6ddad2dab7873ba56a', 'examples/mixed_check.json': 'ea3d0e1669b4eb278d06ea0d951f8d9b6e5cd927695e5f63730cac039d1b8fbf', 'examples/mixed_radius_one_certificate.json': '3a9ec2aec6e6c4bdd26462ffd235ae080195438eb381c1d3c6a455019cbded52', 'examples/mixed_radius_one_check.json': '2d27adc0c0dbf7dd4ea23b1fa6d7539f07ad100887ec2895014d2fea1296f801', 'examples/mixed_radius_one_request.json': 'ce38134afc1bea1db1a7a68600e00bfe4c067537acce1b98d7347e2c6b5a5721', 'examples/mixed_radius_one_witness.json': '0fe40c5256302f7e162a8257406b9ef1177132e5432b2478d3f34ac337096874', 'examples/mixed_request.json': '405f02175080d3065a9750a07be770de91e81ac1ccfbea5a38d2d9a376049c8e', 'examples/mixed_witness.json': 'd9fe237ea42f3a3a4c94ce7e8eaab191dc69e5150d17aecb97e8f3330f5ce133', 'examples/rule_index.json': '6a2757e7c7a8470eea6fc6e766bcffba6783a6d10c8d5b7891a2c69aeb286254', 'examples/trap_rule.json': '6d887415a01414fbfa4297efe0a55cbe7c162dbb7f18acd0e49e2572a3b22f69', 'receipts/certificate-hardening.json': '3d233d020cb7d17eb49b92e26ed62343f8008d17216cf28eaee56d85115c9fe7', 'receipts/certificate-tests.json': '2dda1d38e3485ab0c55c9069d8798f086c99a3fcc94783608b2ce941441cb312', 'receipts/checker-mutations.json': '4d38b245e43307908650b5ab2329f3bcf1a2b86ffa86a2a3fb1e7e2433650d8c', 'receipts/clock-scale-optimized-tests.json': '21fac8478f90e2bf67e59eeacd75348fd4513558d755799a81424c3693e7bfd0', 'receipts/clock-scale-tests.json': '165d82dfd080ef47031faf47a355fddbd22be8b267adb0e1fe2d520b4cbea502', 'receipts/generator-tests.json': 'ff01031c3a2f8c7a0469249a059ba54681287f930e339ab12fd3cec250d883d9', 'receipts/independent-ca-tests.json': '3b5a64d1bbe0858e0ddfa713c7062cf141c291643dcc9854ec7d688b0cbf332d', 'receipts/independent-certificate-tests.json': '83db4e3fb086cefcaabe4926a39f816ba01e4401b8638bc905a23e4bda46485e', 'receipts/literal-export-check.json': '005b519797d8de8ce55de23312b8b06a62240548484c3b6541f2c5334b1ecec3', 'receipts/literal-export.json': '917ddc045bf55e64c9375fd1718b7ad524513b0470fb27418a144f3a88f2a9cf', 'receipts/pdf-qa.json': '5e8b15f223a0a885936d78e06cd6c9ccfcdc24a14f4ffa03e935adf29aeb4bee', 'receipts/radius-one-boundaries.json': '7f4e5f93e8058727eee447e7056901c9ee24bc10e42c3e976a8e41adfed8524b', 'receipts/radius-one-tests.json': '46f8d1498ce37020de44e9e1a01046a5cba132cede783af1f016d6bf64e70ca1', 'receipts/replay-summary.json': 'ad5c09c2b6927ae8c3b2174785e2ae8e00bd004c8586a4b3c8e8e5213f309fad', 'receipts/size-ledger-tests.json': '8373305f7ff33ad3d302ea07d6d74b0b6bfb25a3b5d1bc8ddadb6c030e60a7d6', 'receipts/spatial-radius-one-optimized-tests.json': '4e7787d0745349e23709fcaf5a456193bee1ad5c9f1b8291658c56aa98cda1c0', 'receipts/spatial-radius-one-tests.json': 'a412e34398caf19c2d63efe0143feb76e2c9ddf22db3dd3ba03e6fe882abe890', 'receipts/two-mass-arithmetic-tests.json': 'b52614cf5c469e7132cda508325c37d7dfee71268a053d2ba5cdbb5706440e1c', 'replay.sh': '449ba5b4a70e584aec6d8bfb8691cb312a01c8cf07ec421722673a7debcff847', 'tex/certificate.tex': 'c28e8ea4de307a7c370d23fcb3768757ea69964332fc68e57f1345bc03484d50', 'tex/report.tex': '294682b91792c16bc808fb8a4abf3739c6f61672a7c09c9524cc8debe363162e', 'tex/slowdown.tex': 'a942412a0b042e0c078096ec90a426d84a6ec8b19b8631ef258df60988945c3f', 'tex/verification.tex': '360676465371f47e91b73032c469205fa2a56de9a0000c0154fc56f9d0a1decc', 'three-mass-report.pdf': '1fcaf9a57234e14a2d5d8dc6bc5ec33d50fd7ddc296dc36a67513e61533d4fba', 'three-mass-report.tex': '8bfdbf66399fa40bd4219497abb11c78cfece41b0a4270d9d742ad7111f7930b', 'verify_manifest.py': '43c547c6934c4cbe7e00ebcce57287950a802ede237beacb2b4eaeb9347da48b'}}, 'Exact_Targets_Three_Mass_Units.zip': {'sha256': 'd69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc', 'prefix': 'clean-target-release/', 'members': {'CLEAN-TARGET-THEOREM.md': '3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168', 'README.md': '0ed98f25d5ef8eb7ace2d5062dc4133bf91359892a478b5e5e6fc8159f64cb56', 'SHA256SUMS': '8fabc9b7286d337537ed4c3f6d2d91e5f01701a9dcf98da0833d98abade301af', 'SOURCE_PROVENANCE.md': '64ad83a22114d36080eebc7bdaa4c6364f68045209a7cdae5c07e2b5dedd2121', 'audit/INDEPENDENT-AUDIT.md': '463740467235f6fbade0e35b4300768577b77f996dbd42f21f658f4c73b1024a', 'audit/audit_actual_ca.py': 'd2cd8aaf4c785eb72c0026e51124cb5c9cf574e60d3a56026040e534b7e1f244', 'audit/audit_certificates.py': 'b0959d1bbb5713add367ad557abb1872bfbef33ebf03ef16bc51dce0808a17f1', 'audit/audit_lift_name_collisions.py': '7ee6d1789d3cd50cf40037e16999fdf009dfada6656e13620843dc4db6ccae6f', 'audit/audit_witness_lift.py': '178c5bc0869bdcc22edc5e03d00930ce080440c7ca6461ff765612d3c277b542', 'build.sh': '6139e77ffc095c3c9ad54963043b99588a3e33a562ce02da79722ee38855e799', 'check_clean_targets.py': '51ce0665dcc74bc3cf2461a25344a8688b23258b9281205c68fabb0526881d72', 'clean-target-report.pdf': 'ba7fea2fc0b2fcbc66caa0fe6ec08a1c5121f99be6517a4017e75eb34d4e3332', 'clean-target-report.tex': '363b4bd750a7cec9500273921f6a946844341d40fe9153d03dc7824788881f3a', 'clean_targets.py': 'a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315', 'examples/chain_certificate.json': '54164bdf242bae08cd77e2eb6de308af3589389a009c7ede17366725e6e31074', 'examples/chain_receipt.json': 'bd9f83d07137e3ce20df27f7a73798c23653f99af46fd6a7509bb2d5e1695911', 'examples/chain_request.json': '8e007d4a6061453c2019f9046465186755fd123842fe56152a95452dcf3223e5', 'examples/chain_witness.json': '3e60fe855c11c42408cdd752f746d251a011fc62fccf6fd0b8ecb657f0f54303', 'provenance/source-provenance.json': 'c53e506caa0f0790324d1a62e633cbef43a19f4842d1698dbf6895e1e2488639', 'provenance/upstream-extension-manifest.json': 'b258aeac4ded3aed99bceb2dd1ea293d521bd10991370b78d7e120b9bb767ab3', 'receipts/actual-ca-receipt.json': '8a913a8963b840e60a76509e236d2227745e79a51776511924089a2b6c715f94', 'receipts/affine_lift.json': 'b281476b277f49d3b4deb0a98b51bfd8ce3cd615e4f8a03f916d0ebde28829db', 'receipts/certificate-receipt.json': 'ad98f2e33a89822d9136f7955f04009f57ae8acb5a0619e734cbdf0cd969f069', 'receipts/final-prose-review.json': '60ad5ac07093dc8fbcd2919c51096e538669d0225c0b435804f5a243d56eeb56', 'receipts/lift-name-collision-receipt.json': 'b0bed323c95f6eb368b54e3c8caf39e017163404550e5327f82ca92529de3a6b', 'receipts/portable-replay.json': 'a94e9ba84e00fd6f7e613483462e543130289dbd77de96f5a47c396177ae1b5d', 'receipts/report-qa.json': '92f1d5407f856e602ef77c4e27815b726a790c539ddd7ce964988fea452cf75a', 'receipts/test_clean_targets.json': '0cdab12f6e3dc28b30ae3c26c4f92e39384da8a95b306382d95cb9d3696b50ec', 'receipts/witness-lift-receipt.json': 'aa23dc624fe928302a5748a543e8c4d904bdf3bf9a5feeb80a0c1e8424cbcb45', 'replay.py': '2273e8ef34d2022d1850d3006e195f0e06a31cf50df1ff403411f23097c2c9e9', 'test_affine_lift.py': '385b9015288bfc799ffd22868f786f9fb4edf3c221cd50d0ef5faf9b35e01c3e', 'test_clean_targets.py': 'd6a13ef03a9fb5b7deb64a74eca2f45051f6dc0bcab533b55d675f8af7e3d2eb', 'vendor/certificate.py': 'fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8', 'vendor/checker.py': '9fc3879eb24f4b4d9d2e1c8ebc0c123510c04141bd754547d191ceef28815c66', 'vendor/radius_one.py': '99cae9e9b3d1ceac7b34392e2fe32772daaa88394700ea0c820aa72d3fe5433c', 'vendor/spatial_radius_one.py': '6842cecac0ce20e62d1b0ef18347e52d1db574e11c2d71c3f22a11abf6ae149b', 'vendor/three_mass_collision_generator.py': '14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52', 'verify_manifest.py': 'c242fa8152e71bfd73778a8f891dbca06523974f206476a2b2eb056834710b28'}}}
NATIVE='Three_Mass_Reversible_Computation.zip'
CLEAN='Exact_Targets_Three_Mass_Units.zip'
def need(v,s):
 if not v:raise ValueError(s)
def digest(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def authenticate(root,key):
 root=Path(root);expected=PINS[key]['members']
 for name,pin in expected.items():
  path=root/name;need(path.is_file() and not path.is_symlink() and digest(path.read_bytes())==pin,'Changed package member '+key+':'+name)
 return len(expected)
def unpack(path,key,destination):
 path=Path(path);need(digest(path.read_bytes())==PINS[key]['sha256'],'Wrong archive '+key);expected=PINS[key]['members'];prefix=PINS[key]['prefix'];seen=set()
 with zipfile.ZipFile(path) as z:
  for info in z.infolist():
   name=info.filename;q=PurePosixPath(name)
   need(not q.is_absolute() and '..' not in q.parts and '\\' not in name and str(q)==name.rstrip('/') and not stat.S_ISLNK(info.external_attr>>16),'Unsafe archive member')
   if info.is_dir():continue
   need(name.startswith(prefix),'Unexpected archive root');name=name[len(prefix):]
   need(name in expected and name not in seen,'Unknown or duplicate member');seen.add(name);data=z.read(info)
   need(digest(data)==expected[name],'Member hash mismatch');p=Path(destination)/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 need(seen==set(expected),'Missing archive member');return Path(destination)
@contextlib.contextmanager
def subjects(native,clean):
 names=['certificate','checker','clean_targets','check_clean_targets','three_mass_collision_generator','radius_one','spatial_radius_one']
 old={n:sys.modules.get(n) for n in names};path=list(sys.path);bytecode=sys.dont_write_bytecode
 try:
  sys.dont_write_bytecode=True
  for n in names:sys.modules.pop(n,None)
  loaded={}
  for name,source in [('certificate',native/'code/certificate.py'),('checker',native/'code/checker.py'),('three_mass_collision_generator',native/'code/three_mass_collision_generator.py'),('radius_one',native/'code/radius_one.py'),('spatial_radius_one',native/'code/spatial_radius_one.py'),('clean_targets',clean/'clean_targets.py'),('check_clean_targets',clean/'check_clean_targets.py')]:
   m=types.ModuleType(name);m.__file__=str(source);sys.modules[name]=m;exec(compile(source.read_bytes(),str(source),'exec'),m.__dict__);loaded[name]=m
  yield loaded
 finally:
  sys.path[:]=path;sys.dont_write_bytecode=bytecode
  for n in names:
   if old[n]is None:sys.modules.pop(n,None)
   else:sys.modules[n]=old[n]
def ev(form,values):return sum(c*(values[k] if k else 1) for k,c in form.items())
def poly(cert,values):return sum(ev(x['affine'],values)**2 for x in cert['squares'])+sum(ev(x['left'],values)*ev(x['right'],values) for x in cert['products'])
def expansion(cert):
 out=Counter()
 for a,b in [(r['affine'],r['affine']) for r in cert['squares']]+[(r['left'],r['right']) for r in cert['products']]:
  for x,c in a.items():
   for y,d in b.items():out[tuple(sorted(v for v in (x,y) if v))]+=c*d
 return [{'monomial':list(k),'coefficient':v} for k,v in sorted(out.items()) if v]
def source_trace(machine,initial,N,h):
 q=initial;trace=[(q,N,0)];time=0
 for t in range(h):
  if q==machine.halt:return None
  enabled=[]
  for ins in machine.instructions:
   p=2+ins.counter
   if ins.source==q and not(ins.operation in ('dec','positive') and N%p) and not(ins.operation=='zero' and N%p==0):enabled.append(ins)
  if len(enabled)!=1:return None
  ins=enabled[0];p=2+ins.counter;before=N
  if ins.operation=='inc':N*=p
  elif ins.operation=='dec':N//=p
  time+=96*(before+N)+8+(12*before if ins.operation=='inc' else 12*N if ins.operation=='dec' else 0)
  q=ins.target;trace.append((q,N,time))
 return trace if q==machine.halt else None

def verify(native_root,clean_root):
 native=Path(native_root).resolve();clean=Path(clean_root).resolve();counts=Counter();counts['authenticated_members']=authenticate(native,NATIVE)+authenticate(clean,CLEAN)
 for name in ('certificate.py','checker.py','three_mass_collision_generator.py','radius_one.py','spatial_radius_one.py'):
  need((native/'code'/name).read_bytes()==(clean/'vendor'/name).read_bytes(),'Changed vendored parent');counts['identical_vendor_sources']+=1
 findings=[];examples={}
 with subjects(native,clean) as mods:
  C,K,G,R,S,CT,CK=(mods[n] for n in ('certificate','checker','three_mass_collision_generator','radius_one','spatial_radius_one','clean_targets','check_clean_targets'))
  I,M=C.Instruction,C.Machine
  def reject(fn):
   try:fn()
   except (ValueError,TypeError,KeyError,AssertionError):counts['malformed_rejections']+=1;return
   raise ValueError('Unexpected acceptance')
  # Independent integer interpreter and polynomial expansion across guards/horizons.
  for op,counter in itertools.product(('inc','dec','nop','zero','positive'),(0,1)):
   machine=M(('s','h'),'h',(I('s','h',op,counter),))
   for N,h in itertools.product(range(1,13),range(3)):
    c=C.export_certificate(machine,'s',h,{'mode':'fixed_raw','N':N});B=1+int(op=='zero' and counter==1)
    need(c['ledger']['core_variables']==2*B*h and len(c['squares'])==3*h+1 and len(c['products'])==B*h,'Literal core ledger')
    need(expansion(c)==C.expand_polynomial(c),'Exact coefficient expansion');counts['literal_core_cases']+=1
    trace=source_trace(machine,'s',N,h)
    if trace is None:reject(lambda:C.make_witness(c));counts['false_horizon_or_guard_cases']+=1
    else:
     w=C.make_witness(c);r=K.check(c,w);need(poly(c,w)==0 and [(x['state'],x['N'],x['microtime']) for x in r['source_trace']]==trace,'Integer source semantics')
     counts['accepted_core_cases']+=1
    if h==1 and N<=6:
     zeros=[]
     for values in itertools.product(range(4),repeat=2*B):
      w=dict(zip(c['variables'],values));counts['exhaustive_natural_assignments']+=1
      if poly(c,w)==0:K.check(c,w);zeros.append(w)
     expected=[] if trace is None or max(C.make_witness(c).values(),default=0)>3 else [C.make_witness(c)]
     need(zeros==expected,'Natural zero census')
  # Strong cleanup and affine lift, with ordinary inputs and adversarial names.
  programs=[(M(('h',),'h',()),'h',0),(M(('s','h'),'h',(I('s','h','inc',0),)),'s',1),(M(('s','h'),'h',(I('s','h','zero',1),)),'s',1),
   (M(('s','a','h'),'h',(I('s','a','inc',0),I('a','h','dec',0))),'s',2),
   (M(('F:q','B:q','H'),'H',(I('F:q','B:q','nop'),I('B:q','H','nop'))),'F:q',2)]
  for machine,initial,h in programs:
   wrapped,start=CT.clean_source(machine,initial);B=len(machine.branches())
   inv={'inc':'dec','dec':'inc','zero':'zero','positive':'positive','nop':'nop'}
   expected=[('F:'+i.source,'F:'+i.target,i.operation,i.counter) for i in machine.instructions]+[('B:'+i.target,'B:'+i.source,inv[i.operation],i.counter) for i in machine.instructions]+[('F:'+machine.halt,'B:'+machine.halt,'nop',0),('B:'+initial,'H','nop',0)]
   need([(i.source,i.target,i.operation,i.counter) for i in wrapped.instructions]==expected and len(wrapped.states)==2*len(machine.states)+1 and len(wrapped.branches())==2*B+2,'Literal cleaned program')
   counts['clean_source_tables']+=1
   for model in ('native','spatial-radius-one','phase-radius-one'):
    name='e_0_0' if h==0 else 'e_3_3';tn='u_1_1' if h==0 else 'u_3_3'
    specs=[({'mode':'fixed_raw','N':5},{}),({'mode':'free_raw','name':name},{name:4}),({'mode':'bounded_counters','A':2,'B':1,'a':None,'b':0,'a_name':name},{name:1})]
    for inp,inputs in specs:
     c=CT.export_clean_certificate(machine,initial,h,inp,{'mode':'free','name':tn},model);w=CT.make_clean_witness(c,inputs);r=CK.check(c,w)
     c['expanded_polynomial']=expansion(c);CK.check(c,w)
     f=c['forward_certificate'];N0=ev(f['initial_N'],w);tr=source_trace(machine,initial,N0,h);scale=4 if model=='phase-radius-one' else 1
     need(tr is not None and r['physical_time']==scale*(2*tr[-1][2]+192*(tr[-1][1]+N0)+16) and r['exact_target_N']==N0,'Cleaned clock/target')
     need(c['ledger']['core_variables']==2*B*h and c['ledger']['total_variables']==2*B*h+len(c['input_variables'])+c['ledger']['loader_variables']+1,'Paid compact ledger')
     full,forms=CT.affine_full_witness_lift(c);lifted={n:ev(a,w) for n,a in forms.items()};need(min(lifted.values(),default=0)>=0,'Natural zero lift')
     K.check(full,lifted);need(full['ledger']['core_variables']==8*(B+1)*(h+1),'Full naive ledger')
     manual={n:0 for n in full['variables']};stepnames={z for row in full['steps'] for branch in row for z in (branch['e'],branch['u'])}
     for role in ('input_variables','output_variables'):
      for old,new in zip(c[role],full[role]):need(forms[new]=={old:1},'Coordinate rename map');manual[new]=w[old]
     for n in manual:
      if n not in stepnames and n not in full['input_variables']+full['output_variables']:need(forms[n]=={n:1},'Loader preservation');manual[n]=w[n]
     for t,row in enumerate(f['steps']):
      for b,branch in enumerate(row):
       for key in ('e','u'):
        for target in (full['steps'][t][b][key],full['steps'][2*h-t][B+b][key]):need(forms[target]=={branch[key]:1},'Mirrored affine coordinate');manual[target]=w[branch[key]]
     for t,b,N in ((h,2*B,tr[-1][1]),(2*h+1,2*B+1,N0)):
      row=full['steps'][t][b];manual[row['e']]=1;manual[row['u']]=N-1
     need(manual==lifted,'Independent full zero section');full_inputs={n:manual[n] for n in full['input_variables']};need(C.make_witness(full,full_inputs)==manual,'Unique full witness inverse')
     need(CT.lift_clean_witness(c,w)==(full,lifted),'Public validated lift')
     counts['natural_zero_fiber_bijections']+=1;counts['literal_compact_expansions']+=1
     for field in ('physical_time','exact_target_N','cleaned_source_horizon','ledger','cleaned_machine'):
      bad=copy.deepcopy(c);bad[field]=None;reject(lambda bad=bad:CK.check(bad,w))
     for value in (True,1.0,-1,Fraction(1,2)):
      bad=dict(w);bad[next(iter(w))]=value;reject(lambda bad=bad:CK.check(c,bad))
  # Essential hypotheses demonstrated on exact small counterexamples.
  bad=M(('s','a','h'),'h',(I('s','a','zero',0),I('a','s','inc',0),I('s','h','positive',0)))
  need(source_trace(bad,'s',1,3)==[('s',1,0),('a',1,200),('s',2,508),('h',2,900)],'Freshness counterexample trace');reject(lambda:CT.clean_source(bad,'s'))
  examples['nonfresh_counterexample']={'forward_values':[1,1,2,2],'premature_reverse_exit_N':2,'required_restored_N':1}
  zero=M(('s','h'),'h',(I('s','h','zero',0),));c=C.export_certificate(zero,'s',1,{'mode':'fixed_raw','N':2});w={'e_0_0':1,'u_0_0':Fraction(1,2)}
  need(poly(c,w)==0,'Rational false zero fixture');reject(lambda:K.check(c,w));examples['rational_false_zero']={'operation':'zero2','N':2,'e':1,'u':'1/2','polynomial':0}
  one=M(('s','h'),'h',(I('s','h','inc',0),));c=CT.export_clean_certificate(one,'s',1,{'mode':'fixed_raw','N':1});full,forms=CT.affine_full_witness_lift(c)
  off={n:0 for n in c['variables']};lift={n:ev(a,off) for n,a in forms.items()};need(min(lift.values())==-1,'Offzero lift not globally natural')
  found=None
  for e,u in itertools.product(range(4),repeat=2):
   v={'e_0_0':e,'u_0_0':u};z={n:ev(a,v) for n,a in forms.items()}
   if poly(c,v)!=poly(full,z):found={'e':e,'u':u,'compact_value':poly(c,v),'full_restored_value':poly(full,z)};break
  need(found is not None,'Do not assert offzero polynomial equality');examples['offzero_lift']={'allzero_bridge_minimum':-1,'polynomial_separation':found}
  # Own interpreter for actual collision/stream rows; no producer step/ready calls.
  machine=M(('s','a','h'),'h',(I('s','a','inc',0),I('a','h','dec',0)));wrapped,start=CT.clean_source(machine,'s');ca=G.ThreeMassCA(wrapped.states,wrapped.halt,[G.Instruction(i.source,i.target,i.operation,i.counter) for i in wrapped.instructions])
  q=len(wrapped.states);m=len(wrapped.instructions)+1;d=sum(i.operation in ('inc','dec') for i in wrapped.instructions)
  need((len(ca.names),ca.required_pair_count,len(ca.pairs))==(96*q*m+6*q*d+2*d+6*q+2314,3528*q*m+6*q*d+d-6*m+1152,7008*q*m+12*q*d+2*d+6*q-6*m+2304),'Actual cleaned local-rule counts')
  need(set(ca.pairs)==set(ca.pairs.values()) and len(set(ca.single.values()))==len(ca.names),'Completed finite permutations')
  pinv={b:a for a,b in ca.pairs.items()};sinv={b:a for a,b in ca.single.items()}
  def tick(conf,inverse=False):
   cells=defaultdict(list)
   for x,t in conf:cells[x-ca.velocity[t] if inverse else x].append(t)
   out=[]
   for x,types_ in cells.items():
    ts=tuple(sorted(types_));need(len(set(ts))==len(ts),'Boolean collision')
    z=((sinv if inverse else ca.single)[ts[0]],) if len(ts)==1 else (pinv if inverse else ca.pairs).get(ts,ts) if len(ts)==2 else ts
    out.extend((x if inverse else x+ca.velocity[t],t) for t in z)
   return tuple(sorted(out))
  def canonical(q,N):return tuple(sorted([(-12*N,ca.type_ids['L',0,(q,0,0)]),(-12*N,ca.type_ids['S',0]),(0,ca.type_ids['R',])]))
  c=CT.export_clean_certificate(machine,'s',2,{'mode':'fixed_raw','N':5});w=CT.make_clean_witness(c);r=CK.check(c,w);conf=canonical(start,5);target=canonical('H',5);sections={row['microtime']:canonical(row['state'],row['N']) for row in r['cleaned_source_trace']}
  for t in range(1,r['physical_time']+1):
   before=conf;cells=defaultdict(list)
   for x,k in before:cells[x].append(k)
   need(all(len(v)!=2 or tuple(sorted(v)) in ca.specified_pairs for v in cells.values()),'Used completion before target')
   conf=tick(conf);need(len(conf)==3 and tick(conf,True)==before,'Actual inverse/mass');need((conf==target)==(t==r['physical_time']),'First exact target')
   if t in sections:need(conf==sections[t],'Exact source section')
   counts['independent_native_ticks']+=1
  counts['complete_actual_cleanup_runs']+=1
  examples['actual_cleaned_fixture']={'N0':5,'h':2,'first_target_time':r['physical_time'],'types':len(ca.names),'prescribed_pairs':ca.required_pair_count,'completed_pair_support':len(ca.pairs)}
  # Spatial floor division and full mixed-phase inverses, including huge coordinates.
  spatial=S.SpatialRadiusOneCA(ca);phase=R.RadiusOneCA(ca,4);rng=random.Random(803)
  for j in range(48):
   conf=tuple(sorted(set((rng.choice((-2**80,-5,-1,0,7,2**80)),rng.randrange(len(ca.names))) for _ in range(1+j%7))))
   b=spatial.embed(conf);need(spatial.project(b)==conf and spatial.project(spatial.step(b))==tick(conf),'Full spatial conjugacy');need(spatial.inverse_step(spatial.step(b))==b,'Spatial inverse')
   z=tuple((x,4*t+rng.randrange(4)) for x,t in conf);need(phase.inverse_step(phase.step(z))==z,'Mixed-phase inverse');counts['mixed_wrapper_cases']+=1
  # Integer pseudo-coefficients cannot cross either intended verifier boundary.
  for checker,cert in ((K,C.export_certificate(one,'s',1,{'mode':'fixed_raw','N':2**100})),(CK,CT.export_clean_certificate(one,'s',1,{'mode':'fixed_raw','N':2**100}))):
   wit=C.make_witness(cert) if checker is K else CT.make_clean_witness(cert)
   for typ in (float,bool):
    bad=copy.deepcopy(cert);form=bad['squares'][0]['affine'];k=next(iter(form));form[k]=typ(form[k]);reject(lambda bad=bad,checker=checker,wit=wit:checker.check(bad,wit))
 for key,root in ((NATIVE,native),(CLEAN,clean)):authenticate(root,key)
 return {'status':'PASS_BATCH80_THREE_MASS','archive_sha256':{k:v['sha256'] for k,v in PINS.items()},'members':{k:len(v['members']) for k,v in PINS.items()},'independent_counts':dict(counts),'examples':examples,'findings':findings,
  'scope':'Mathematical/source review with finite independent checks; three typed mass units are not three scalar witnesses. Natural quadratic certificates retain an external source horizon. Exact-target lift is a zero-fiber bijection only. No numerical universal source, priority claim or fixed-arity arithmetic record.'}

IGNORED_METADATA={'elapsed_seconds','python'}
def normalized(obj):
 if type(obj)is dict:
  return {k:(Path(v).name if k in ('generator_path','source_file') and type(v)is str else normalized(v)) for k,v in obj.items() if k not in IGNORED_METADATA}
 if type(obj)is list:return [normalized(x) for x in obj]
 return obj
NATIVE_RECEIPTS={
 'generator-tests.json':'generator-tests.json','independent-ca-tests.json':'independent-ca-tests.json','size-ledger-tests.json':'size-ledger-tests.json',
 'certificate-tests.json':'certificate-tests.json','independent-certificate-tests.json':'independent/receipt.json','checker-mutations.json':'independent/checker-receipt.json',
 'certificate-hardening.json':'independent/hardening-receipt.json','radius-one-tests.json':'radius-one-tests.json',
 'spatial-radius-one-tests.json':'spatial-radius-one-tests.json','spatial-radius-one-optimized-tests.json':'spatial-radius-one-optimized-tests.json',
 'clock-scale-tests.json':'clock/scale-receipt.json','clock-scale-optimized-tests.json':'clock-optimized/scale-receipt.json',
 'two-mass-arithmetic-tests.json':'two-mass-arithmetic-tests.json','literal-export-check.json':'literal-export-check.json','literal-export.json':'literal-export.json','replay-summary.json':'replay-summary.json'}
def author_evidence(native,clean,native_out,clean_receipt):
 native,clean,native_out,clean_receipt=map(Path,(native,clean,native_out,clean_receipt));comparisons={}
 for published,fresh in NATIVE_RECEIPTS.items():
  a=json.loads((native/'receipts'/published).read_text());b=json.loads((native_out/fresh).read_text())
  need(exact(normalized(a),normalized(b)),'Native author receipt changed '+published)
  comparisons[published]=digest(json.dumps(normalized(b),sort_keys=True,separators=(',',':')).encode())
 exports=[]
 for p in sorted((native/'examples').glob('*.json')):need(p.read_bytes()==(native_out/'examples'/p.name).read_bytes(),'Literal native export differs');exports.append(p.name)
 fresh=json.loads(clean_receipt.read_text());need(fresh['status']=='passed' and len(fresh['commands'])==11 and all(r['returncode']==0 for r in fresh['commands']) and fresh['literal_examples_byte_identical'],'Clean author replay failed')
 clean_comp={}
 for name,b in fresh['receipts'].items():
  a=json.loads((clean/'receipts'/name).read_text());need(exact(normalized(a),normalized(b)),'Clean author receipt changed '+name)
  clean_comp[name]=digest(json.dumps(normalized(b),sort_keys=True,separators=(',',':')).encode())
 authenticate(native,NATIVE);authenticate(clean,CLEAN)
 return {'native':{'status':'PASS','normalized_receipts':comparisons,'literal_example_files':exports,'published_members_unchanged':66},
  'clean':{'status':'PASS','commands':fresh['commands'],'normalized_receipts':clean_comp,'literal_examples_byte_identical':True,'published_members_unchanged':38},
  'normalization':{'ignored_metadata_fields':sorted(IGNORED_METADATA),'basename_metadata_fields':['generator_path','source_file'],'all_other_values_exact':True}}
def run_authors(native,clean):
 with tempfile.TemporaryDirectory(prefix='three-mass-review-authors-') as directory:
  work=Path(directory);N=work/'native';C=work/'clean';shutil.copytree(native,N,ignore=shutil.ignore_patterns('__pycache__','.replay','.build'));shutil.copytree(clean,C,ignore=shutil.ignore_patterns('__pycache__','.replay','.build'))
  env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHON':sys.executable};env.pop('PYTHONOPTIMIZE',None)
  for root in (N,C):subprocess.run([sys.executable,'verify_manifest.py'],cwd=root,env=env,check=True,capture_output=True,text=True)
  with (work/'native.log').open('w') as log:subprocess.run(['sh','replay.sh',str(work/'native-output')],cwd=N,env=env,check=True,stdout=log,stderr=subprocess.STDOUT)
  with (work/'clean.log').open('w') as log:subprocess.run([sys.executable,'replay.py','--receipt',str(work/'clean.json')],cwd=C,env=env,check=True,stdout=log,stderr=subprocess.STDOUT)
  return author_evidence(N,C,work/'native-output',work/'clean.json')

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--native-archive',type=Path);p.add_argument('--clean-archive',type=Path);p.add_argument('--native-root',type=Path);p.add_argument('--clean-root',type=Path);p.add_argument('--authors',action='store_true');p.add_argument('--native-replay',type=Path);p.add_argument('--clean-replay',type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
 with tempfile.TemporaryDirectory(prefix='three-mass-review-') as directory:
  if a.native_archive or a.clean_archive:
   need(a.native_archive and a.clean_archive and not a.native_root and not a.clean_root,'Supply both archives or both extracted roots')
   native=unpack(a.native_archive,NATIVE,Path(directory)/'native');clean=unpack(a.clean_archive,CLEAN,Path(directory)/'clean')
  else:
   need(a.native_root and a.clean_root,'Supply both archives or both extracted roots');native=a.native_root;clean=a.clean_root
  result=verify(native,clean)
  if a.authors:
   need(not a.native_replay and not a.clean_replay,'Fresh author replay versus existing replay evidence are exclusive');result['author_replays']=run_authors(native,clean)
  elif a.native_replay or a.clean_replay:
   need(a.native_replay and a.clean_replay,'Supply both recorded author outputs');result['author_replays']=author_evidence(native,clean,a.native_replay,a.clean_replay)
  result['review_source_sha256']=digest(Path(__file__).read_bytes())
  if a.expect:need(exact(result,json.loads(a.expect.read_text())),'Saved review receipt mismatch')
  if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
  print(json.dumps({'status':result['status'],'independent_counts':result['independent_counts'],'author_replays':'author_replays'in result},indent=2))
if __name__=='__main__':main()
