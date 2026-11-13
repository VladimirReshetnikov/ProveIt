#!/usr/bin/env python3
"""Exploratory one-module check; inherited provider is not a source rebuild."""
from pathlib import Path
from hashlib import sha256
import json,os,shutil,subprocess,sys,tempfile,time
if sys.flags.optimize: raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent; a=os.environ.get('ATTEMPT','attempt01')
if not a.startswith('attempt') or not a[7:].isdigit():raise SystemExit('bad attempt name')
obs=H/'observations'/('cabovex-'+a)
if obs.exists():raise SystemExit('observation exists')
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');lib=Path('/tmp/direct90-ipra-join-b66u_qqo/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');source=H/'Direct80CAboveX.lean';provider=lib/'DiophantineConsistency/ArithmeticGcdNormalization.olean'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
 leanps=[x.strip() for x in ps if len(x.split(None,3))>1 and x.split(None,3)[1]=='lean']
 mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
 return {'lean':leanps,'mem_available_kib':mem,'time_ns':time.time_ns()}
need=lambda b,m:None if b else (_ for _ in ()).throw(RuntimeError(m))
need(lean.is_file() and provider.is_file() and pkg.is_dir(),'missing tool/provider')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
extra=[Path('/tmp/tenpositive-80fold-complete-_pnqkowv/Direct80Fold.olean'),Path('/tmp/tenpositive-80consequences-v4thmrx1/Direct80Consequences.olean'),Path('/tmp/pell-all-index-recovery-oi9pydkd/PellRecovery.olean'),Path('/tmp/pell-all-index-odd-fold-t52feqmz/PellOddFold.olean'),Path('/tmp/pell-all-index-fold-ad1a76zq/PellFold.olean'),Path('/tmp/tenpositive-80joined-jvu6i1ua/Direct80Joined.olean'),Path('/tmp/tenpositive-80residue-binding-9cls2v_d/Direct80ResidueBinding.olean'),Path('/tmp/tenpositive-80residue-wmjxeubh/Direct80Residue.olean'),Path('/tmp/tenpositive-80adjacent-dhdsags5/Direct80Adjacent.olean'),Path('/tmp/tenpositive-adjacent-integer-uhhde7iz/AdjacentInteger.olean'),Path('/tmp/tenpositive-adjacent-complete-w9h57aeb/AdjacentComplete.olean'),Path('/tmp/tenpositive-adjacent-step-r3dpq5z3/AdjacentStep.olean'),Path('/tmp/tenpositive-adjacent-bounds-tceau5u7/AdjacentBounds.olean'),Path('/tmp/tenpositive-adjacent-nk5miisb/AdjacentDenominator.olean'),Path('/tmp/tenpositive-adjacent-preserve-9uy_qhmf/AdjacentPreserve.olean'),Path('/tmp/tenpositive-80factors-wjl9x3rl/Direct80Factors.olean'),Path('/tmp/tenpositive-80root-vb74zjn5/Direct80Root.olean'),Path('/tmp/tenpositive-80graph-d2v79zbc/Direct80Graph.olean'),Path('/tmp/tenpositive-product-root-kdq8sqms/ProductRoot.olean'),Path('/tmp/tenpositive-doubling-z_t6ngdp/TenPositiveDoubling.olean'),Path('/tmp/tenpositive-scaledsquare-rat00ki8/ScaledSquare.olean')]
expected=['40c76ff3acfa34f04930608ae981619c5a958ad8d280945a2b64f877906d8571','c94ec3204581fd951c3380b01d5a7643b07c18d530712898378ccac17e1763ac','0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a','853721216a20dbf04c1babafbbb79526d92db0aee5f3a6127625d86208bc3175','302aefad9e2d7a9b4fce22e989d4c4a791f3e79ef83cb6f245a2ed0ed1b4140e','2caa748fef16dab60c71d492f40f59dcf402bac44b0ab4907cfe742c957cd081','59abd5fea088f3d884d83c23d23b5086227780c4a2fa6fce0daea2a518650411','89439c2c076fa9b652dce331652e13bdb6ad3a896cadf82a4d445dbb4288ccf4','26d181ad42cacd5f8749e0d97fcfae90660b87601574745d48fd2f815f8c98ad','19321c96c92462072fc3fe6cf30212535baa29e7915e1e59ca2c26073873dc34','e75ae912b24068b600e79d93eaef81e314146b7b50e0c4268c2f6db6fd0e650b','cf3fee46a9e362a5b474f1d983c25e7dc67cb65436b3c4f0625ecf1cf17710a7','b6afea28cda32503292760953f1773b183089b151689af8f80d1d76a18da8101','83c7300a38a6d5619d9802679be749fbe8088a1be0e34c3683aecd7965dc9ff9','bf2cef6fd83385d21a3553ca2a774273bf9b8febb0c6dedae2ef40c5e8e2e2e2','3703cad8beb421022aba3a80849f71c90b77d603e4567164652d72f2e8f954a0','6cb873420b53fcfa692f16c59d35941a4c56f78f70ab26a3684e33adaa2509c0','95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4','92dbb47e969d3603f6f496f53c7995493a989293a37e5272c308ff79d3fb09d5','138dbf9563aab2a4b867547b8f2ee9650faec64b2f403c17b1598b11db66522f','37ce988b94587130947097a868dd153f5564718dd280fafe6fd3b75aa2028691']
extra+=[Path('/tmp/absorb89-chain-8h1sfgle/lib/Direct80ScaledGrowthMinus.olean'),Path('/tmp/tenpositive-80pell-0pa7bo8q/Direct80Pell.olean'),Path('/tmp/tenpositive-80mainnorm-uewlhem5/Direct80MainNorm.olean')]
expected+=['2eec905d0c1eff64395322328a3ee0e7ad30d08c169990e9b74e578affbc826e','764c9ce5f5f8e55323128ef195307ca030eee2596bd6eda283a6e0fc2be97807','817aca133ff759ad633835741f261503a2612cd5a0e95de274bcce1bd607593a']
extra.append(Path('/tmp/absorb89-chain-76k5jp49/lib/Direct80IndexOne.olean'))
expected.append('f439752ad98d0b0c2f1ece874cfd46d4a340f84d34a9dd644e95910bf4d14db7')
extra.append(Path('/tmp/tenpositive-80graphindex-vb3yq5ei/Direct80GraphIndex.olean'))
expected.append('e9a8f99e13f8929d4f63380ceed2deed49a8fd6e65f50ab2146add94b153deb2')
pins={'source':sha(source),'runner':sha(Path(__file__)),'lean':sha(lean),'direct_provider':sha(provider),'extra':[sha(x) for x in extra]}
need(pins['extra']==expected,'prototype provider changed')
need(pins['direct_provider']=='254b88abe787829f8bfad61f9606a14318cb31186b593e0cb76821e4e1ad1242','direct provider changed')
obs.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='tenpositive-80cabovex-'));copy=out/source.name;shutil.copyfile(source,copy);shutil.copyfile(source,obs/'source.txt')
cmd=[str(lean),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'Direct80CAboveX.olean')]
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'/tmp/tenpositive-80graphindex-vb3yq5ei:/tmp/absorb89-chain-76k5jp49/lib:/tmp/absorb89-chain-8h1sfgle/lib:/tmp/tenpositive-80pell-0pa7bo8q:/tmp/tenpositive-80mainnorm-uewlhem5:/tmp/tenpositive-80fold-complete-_pnqkowv:/tmp/tenpositive-80consequences-v4thmrx1:/tmp/pell-all-index-recovery-oi9pydkd:/tmp/pell-all-index-odd-fold-t52feqmz:/tmp/pell-all-index-fold-ad1a76zq:/tmp/tenpositive-80joined-jvu6i1ua:/tmp/tenpositive-80residue-binding-9cls2v_d:/tmp/tenpositive-80residue-wmjxeubh:/tmp/tenpositive-80adjacent-dhdsags5:/tmp/tenpositive-adjacent-integer-uhhde7iz:/tmp/tenpositive-adjacent-complete-w9h57aeb:/tmp/tenpositive-adjacent-step-r3dpq5z3:/tmp/tenpositive-adjacent-bounds-tceau5u7:/tmp/tenpositive-adjacent-nk5miisb:/tmp/tenpositive-adjacent-preserve-9uy_qhmf:/tmp/tenpositive-80factors-wjl9x3rl:/tmp/tenpositive-80root-vb74zjn5:/tmp/tenpositive-80graph-d2v79zbc:/tmp/tenpositive-product-root-kdq8sqms:/tmp/tenpositive-doubling-z_t6ngdp:/tmp/tenpositive-scaledsquare-rat00ki8:{lib}:{pkg}','LEAN_NUM_THREADS':'1'}
samples=[];start=time.monotonic();reason=None
with (obs/'stdout').open('x') as so,(obs/'stderr').open('x') as se:
 p=subprocess.Popen(cmd,stdout=so,stderr=se,env=env)
 try:
  while p.poll() is None:
   sample=resources();samples.append(sample)
   if len(sample['lean'])>2 or sample['mem_available_kib']<8*1024**2:reason='resource guard';break
   if time.monotonic()-start>180:reason='timeout';break
   time.sleep(2)
 except Exception as exc:reason='monitor error '+repr(exc)
 finally:
  if reason and p.poll() is None:p.kill()
  p.wait()
obj=out/'Direct80CAboveX.olean';after={'source':sha(source),'runner':sha(Path(__file__)),'lean':sha(lean),'direct_provider':sha(provider),'extra':[sha(x) for x in extra]}
result={'command':cmd,'lean_path':env['LEAN_PATH'],'output_root':str(out),'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'pins':pins,'after':after,'preflight':pre,'samples':samples,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'object_sha256':sha(obj) if obj.is_file() else None,'scope':'exploratory author check; direct input pinned, inherited project/package/dynamic/source-object ancestry; no graph or iPRA endpoint'}
(obs/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('exit','reason','output_root','object_sha256')}))
print((obs/'stdout').read_text());print((obs/'stderr').read_text(),file=sys.stderr)
need(p.returncode==0 and reason is None and obj.is_file() and pins==after and not any(x in (obs/'stdout').read_text()+(obs/'stderr').read_text() for x in ('error:','warning:','sorryAx')),'Lean check failed')
