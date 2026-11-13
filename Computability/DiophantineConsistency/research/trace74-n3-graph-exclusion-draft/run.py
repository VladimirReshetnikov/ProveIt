#!/usr/bin/env python3
"""HELD: three-stage exploratory check; requires scoped review and slot release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SCALAR=Path('/tmp/trace74-symbolic-fixed-mask-cover-uh7rokqo/lib');ODDFIVE=Path('/tmp/trace74-n3-odd-five-r8infjcc/lib');FIFTH=Path('/tmp/trace74-n2-fifth-growth-ndmy3hdn/lib');GRAPH=Path('/tmp/trace74-graph-index-upper-sbqz0413/lib');GROWTH=Path('/tmp/absorb89-chain-8h1sfgle/lib');UPPER=Path('/tmp/trace74-index-upper-lw94r446/lib');ORDER=Path('/tmp/trace74-index-order-vu44__7n/lib');RESIDUE=Path('/tmp/trace74-guardfree-residue-9rz_sl3r');CARRIER=Path('/tmp/trace74-guardfree-offset-g91osrrh/lib');ODD=Path('/tmp/trace74-odd-ordinate-bound-b8rmryeu/lib');FOLD=Path('/tmp/trace74-guardfree-fold-mqg70pbn/lib');ADJ=Path('/tmp/trace74-guardfree-adjacent-e85cpupi/lib');PELL=Path('/tmp/trace74-guardfree-pell-jg0_m3mj');ROOTS=Path('/tmp/trace74-arbitrary-root-wppvu6hp/lib');BASE=Path('/tmp/trace74-direct-four-block-1zltaw2f/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={BASE/'DiophantineConsistency/ArithmeticPellCongruences.olean':'ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664',GROWTH/'Direct80ScaledGrowthMinus.olean':'2eec905d0c1eff64395322328a3ee0e7ad30d08c169990e9b74e578affbc826e',BASE/'DiophantineConsistency/ArithmeticPellFirstIndex.olean':'20d3769d891a42810c1985203768b122bf936884494d2829415e3140d6deb9c2',H/'Trace74N3GraphExclusion.lean':'14482fb8cd968a378a7833600d417cc9ffa0b24e7ecc7dd61f347f05b81cec3b',SCALAR/'Trace74N3ScalarDiscrete.olean':'1cbc0a63ccf24cc5b36f97f970abb3a7b96f26a1cc64b26179e96c8ef655e93a',ODDFIVE/'Trace74N3OddFive.olean':'96f14503fde3d87a3c60ba57cf92aaab7549ec8849201c39f1da04113a11443d',FIFTH/'Trace74N2FifthGrowth.olean':'defa084264b6fdccc0af1130947d29cf187be6010dfb2851cf2a8ef687ff649a',H.parent/'trace74-n3-scalar-discrete-v2-rebuild/observations/attempt01/result.json':'c56f50101472e542385769a4b8c69715483d3a00c9aa5f439d29be6accceb637',H.parent/'trace74-n3-scalar-discrete-v2-rebuild/observations/outer-attempt01/terminal.json':'92e15a214c3d33140141c2f30c7b0f0b5f695d5274b44bd313551909f9f9aa70',H.parent/'trace74-n3-odd-five-draft/observations/attempt01/terminal.json':'19b99f8e788dd0e60f69332839e04b8a2f9ae212c27db7f0b7fb796a1edc7ad2',H.parent/'trace74-n2-fifth-growth-draft/observations/attempt02/terminal.json':'8191707c6ced991f0fa886052f4e1d56851387284f73daf45bd6bcc4de2aaf0b',GRAPH/'Trace74GraphIndexUpper.olean':'f374cb930e6a466f2c9b08e72b51555d734dedfab884174a43bbc09b5c8b457c',H.parent/'trace74-index-upper-draft/graph-observations/attempt01/terminal.json':'a63718a301ce20352b039eea8920e23b989b2a13acaf404026da8c881789290f',UPPER/'Trace74IndexUpper.olean':'c5e744f44413bd6c5dc7ed40d228092d857da3d361cfaa2dca0595109200c918',ORDER/'Trace74IndexOrder.olean':'41147d2a21ad53a9027d36bcb4d7a349974894e7f3e4b1ad1b16395dd785920c',H.parent/'trace74-index-upper-draft/observations/attempt04/terminal.json':'0f539f779805a678b238bb05abe1c1acc6fa4df6d0d295c159689e71edf794ea',H.parent/'trace74-index-order-draft/observations/attempt02/terminal.json':'1babb66c4fec1944f29a762189d559e2d5fe4975f26f2acc94e890b0944135ac',RESIDUE/'Trace74FirstIndexResidue.olean':'9155e2a4d9a945750f1edb1af9ce985d4b6f5ff55323b68a82a83ec3724d288f',H.parent/'trace74-arbitrary-root-draft/residue-observations/attempt01/terminal.json':'3c7ed7084bbe5528b768de2084271d0293e7b5fd247410450da59c1d83e0c4f3',BASE/'Direct80ProjectionProduct.olean':'25b274e6e2e8d7770a2b33f8ce83f8a40c77f68b9cd98d19fb82c928a4643690',CARRIER/'Trace74CarrierBound.olean':'dd0e99f93eced01bf479592d2c9a76efc86b29d3a17b28c2daede3ed5719c8e4',H.parent/'trace74-guardfree-adjacent-draft/offset-observations/attempt03/terminal.json':'8152cf17eafb3f2520a7063e8de1e8814894bc9215575dfe135f4260410e0ca9',FOLD/'Trace74Index.olean':'e18df61ea16cd2cbf0f7650a415d9f6fcc171d181e94e0bd3c90de6839ea175a',H.parent/'trace74-odd-ordinate-bound-draft/observations/attempt02/terminal.json':'833d7fd8dd39cbb38d4f1fad72835e9b07797e9dee95696600d92cd476be9b55',ODD/'Trace74OddOrdinateBound.olean':'a619576cc62abcde2dc1c57f779fe8a8d6ecf0276180e23f17bc0fdbd6a96caa',H.parent/'trace74-guardfree-fold-draft/observations/attempt02/terminal.json':'e29bb3bd247a09dea6512ac0f119d8d094a2dc9b13727649ae816e6b444ff14b',FOLD/'Trace74Fold.olean':'e22ec29b543b0f4e77b2ebdd8c2864056f51faad778917dadb0d802c30107956',FOLD/'Trace74Joined.olean':'f6f71d8238abd94fc38d4bb1999fd5788f0d59a70a1e0cb0254db6706cd05a69',ADJ/'Trace74Representatives.olean':'ea48131f0f0ec2d4e7d3a3fea37e9b4cb676b7e6e2eb1a296c8573247979d86e',ADJ/'Trace74Adjacent.olean':'f3a04fb5e9368c1bf3b663b059c0a82818256e0f09b036c493bde6906b4323b5',ADJ/'Trace74Residue.olean':'35146b81c45e7a2f88debb74b3fbf1c47571f7644905f6a820a2cea616e723cc',PELL/'Trace74Pell.olean':'9d4091ba1b0de184e0d454eb3dc1f5f3bf0810e1ddd08d186dfd550cb44fe3d0',ROOTS/'Trace74GraphRoots.olean':'416dd86090bca9dc40d2dcf2836c58a9c512357a142d2612e2307e660347446c',BASE/'PellRecovery.olean':'0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a',BASE/'DiophantineConsistency/ArithmeticPellHalfIndex.olean':'6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CORE/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
STAGES=[('Trace74N3GraphExclusion',['Trace74N3GraphExclusion.graph_first_three_impossible'])]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in lines if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def verify():
 for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
def report_ok(text,names):
 body=r" (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))"
 pat=r"\s*"+r"\s*".join("'"+re.escape(n)+"'"+body for n in names)+r"\s*"
 m=re.fullmatch(pat,text,re.S)
 if not m:return False
 for i in range(len(names)):
  group=m.group(1+2*i)
  if group is None:continue
  parts=[x.strip() for x in group.split(',')]
  if not parts or any(not x for x in parts) or len(parts)!=len(set(parts)) or not set(parts)<={'propext','Classical.choice','Quot.sound'}:return False
 return True
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify preflight-only or attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
verify();runhash=sha(__file__);pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'resource preflight')
if args.preflight_only:
 print(json.dumps({'status':'PASS','pins':{str(p):h for p,h in PINS.items()},'runner_sha256':runhash,'resources':pre,'scope':'pin and live resource preflight only; no Lean invocation'},sort_keys=True,indent=2));sys.exit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
verify();pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'locked resource preflight')
obs=H/'observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False);root=Path(tempfile.mkdtemp(prefix='trace74-n3-graph-exclusion-'));lib=root/'lib';lib.mkdir()
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=':'.join(map(str,(lib,ODDFIVE,FIFTH,GRAPH,UPPER,ORDER,RESIDUE,CARRIER,ODD,FOLD,ADJ,PELL,ROOTS,BASE,SCALAR,GROWTH,PACK)))
records=[];overall='PASS'
for idx,(module,report) in enumerate(STAGES,1):
 outpath=obs/f'stage-{idx:02d}.stdout';errpath=obs/f'stage-{idx:02d}.stderr';obj=lib/(module+'.olean')
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(H),str(H/(module+'.lean')),'-o',str(obj)];samples=[];reason=None;start=time.monotonic()
 with outpath.open('x') as out,errpath.open('x') as err:
  proc=subprocess.Popen(cmd,env=env,stdout=out,stderr=err)
  try:
   while proc.poll() is None:
    time.sleep(1);s=resources();samples.append(s)
    if s['mem_available_kib']<8*1024**2 or len(s['lean'])>1:reason='resource guard';proc.kill();break
    if time.monotonic()-start>120:reason='timeout';proc.kill();break
  finally:
   if proc.poll() is None:proc.kill()
   proc.wait()
 out=outpath.read_text();err=errpath.read_text();ok=proc.returncode==0 and reason is None and obj.is_file() and report_ok(out,report) and not err and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',out)
 records.append({'module':module,'expected_report':report,'status':'PASS' if ok else 'FAIL','command':cmd,'exit':proc.returncode,'reason':reason,'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(outpath),'stderr_sha256':sha(errpath),'object_path':str(obj) if obj.exists() else None,'object_sha256':sha(obj) if obj.exists() else None})
 if not ok:overall='FAIL';break
verify();need(sha(__file__)==runhash,'runner changed')
result={'status':overall,'runner_sha256':runhash,'pins':{str(p):h for p,h in PINS.items()},'lean_path':env['LEAN_PATH'],'preflight':pre,'postflight':resources(),'stages':records,'output_root':str(root),'scope':'Same positive graph tuple excludes first Pell index three, with beta at least 31; no guard or endpoint. Direct objects pinned; full project/package/dynamic ancestry and search-path shadowing remain inherited; no fixed-port guard, population, or iPRA theorem.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if overall=='PASS' else 1)
