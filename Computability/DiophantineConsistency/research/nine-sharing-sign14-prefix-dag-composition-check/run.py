#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-sign14-prefix-code-check-20261110');OUT=Path('/tmp/nine-sharing-sign14-prefix-dag-composition-check-20261110');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-sign14-prefix-code-check/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise RuntimeError(msg)
def save():
 t=OUT/'state.tmp';t.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(t,OUT/'state.json')
def guard(modules):
 ret={}
 for n in modules:
  for r in roots:
   for s in suffixes:
    p=r/(n.replace('.','/')+s)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));ret[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:ret[str(p)]=None
 return ret
def check_external_syntax():
 global framework
 need(sha(P/'framework-survey.py')=='6442c87cf40d2f01578675a2b4107006fca0977864cbe0a714c2dc6515c8d332','framework survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'framework-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'framework survey');framework=json.loads(r.stdout);need(framework['status']=='PASS','framework status')
check_external_syntax()
need(sha(D/'research/nine-sharing-sign26-endpoint-retry01/attempt01/state.json')=='8b7490adbdecd01e9d23d3a8978c72d38deb5ef97d931ca1120627acdf2d7003','retry failure receipt')
need(sha(D/'research/nine-sharing-sign14-prefix-reflection-check/attempt01/state.json')=='bf20cda1ca905e59a13348f349bcd450e4ecd30ece9474d760152d23bf8dd6ae','previous failure pin')
need(sha(D/'research/nine-sharing-sign14-prefix-reflection-check/attempt01/outer-result.json')=='9236c005d22d5604da3f8be8a91a4d93f918736532247b4aa5e76c706be1f523','previous failure pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-reflection-terminal-independent/check.py')=='f892e2a4c087fbb17992f0e91b0826dfa3f156f4a606245b07e804a50d0f1b57','previous failure pin')
need(json.loads((D/'research/nine-sharing-sign14-prefix-reflection-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==1,'previous failure outer status')
need(sha(D/'research/nine-sharing-sign14-prefix-reflection-retry01-check/attempt01/state.json')=='5066168d76d191e89637984c9a4763f49c5226de9441d607aaf4d11749bc3c51','retry01 failure pin')
need(sha(D/'research/nine-sharing-sign14-prefix-reflection-retry01-check/attempt01/outer-result.json')=='d72c1c156102e28d95ee94ae65abd13c3dde6c5b5414f00bea7d284912e9f0da','retry01 failure pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-reflection-retry01-terminal-independent/check.py')=='4d5beac661ce62e0bcd4bea4153739a2b582d88c55a084431f1858474ff4948c','retry01 failure pin')
need(json.loads((D/'research/nine-sharing-sign14-prefix-reflection-retry01-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==1,'retry01 outer status')
need(sha(D/'research/nine-sharing-sign14-prefix-reflection-retry02-check/attempt01/state.json')=='8bb39eb62cc9316dd5a456be293846b6272fbc7a467eedb27f6e4487adafdc41','retry02 failure pin')
need(sha(D/'research/nine-sharing-sign14-prefix-reflection-retry02-check/attempt01/outer-result.json')=='800793d407481b45f84d1b364fb12bd3a011bd4240da0b147f108f98478e5212','retry02 failure pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-reflection-retry02-terminal-independent/check.py')=='aac90dfab31c3e567365cdf9ab1e4b7ecd2b736e9316c71a7a652711b4f6db06','retry02 failure pin')
need(json.loads((D/'research/nine-sharing-sign14-prefix-reflection-retry02-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==1,'retry02 outer status')
need(sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/manifest.json')=='19558421ef6ce10151450614213cfb90789b0cd1407ada737e5d97049a94224d','fragment/audit pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-dag-fragments-independent/check.py')=='408c88becb4d9cab4f0d47a42919604890dcfcc202ccfbcb8576cf3e4a4cfcd9','fragment/audit pin')
need(sha(D/'research/nine-sharing-sign14-prefix-dag-lemma-check/attempt01/outer-result.json')=='55f2b5f2b0c1094c36b3f7c8367d17f6d62fa4c2cc50a9072f14e3f8130ef87a','fragment/audit pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-dag-lemma-terminal-independent/check.py')=='e95fa84ff37f3a8cf79af2198c6949d090e62862bcfc786ead4d22e90e24fb6a','fragment/audit pin')
need(json.loads((D/'research/nine-sharing-sign14-prefix-dag-lemma-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==0,'first fragment outer status')
need(sha(P/'src/DiophantineConsistency/fragment000.prefix')=='118dce858ad9198efce02acfa71b64f0729ea1da75619140aafd575baeaed053' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment000.prefix')=='118dce858ad9198efce02acfa71b64f0729ea1da75619140aafd575baeaed053','fragment pin fragment000.prefix')
need(sha(P/'src/DiophantineConsistency/fragment001.prefix')=='5f19afc99d0b65bd9f6dbc8eb629875f34f474f8d24868bce56635a11caeac49' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment001.prefix')=='5f19afc99d0b65bd9f6dbc8eb629875f34f474f8d24868bce56635a11caeac49','fragment pin fragment001.prefix')
need(sha(P/'src/DiophantineConsistency/fragment002.prefix')=='5cc4a464b94e50c4e73286aa3a36b6218c7e27ad3b548ab7ae782aa1252ad820' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment002.prefix')=='5cc4a464b94e50c4e73286aa3a36b6218c7e27ad3b548ab7ae782aa1252ad820','fragment pin fragment002.prefix')
need(sha(P/'src/DiophantineConsistency/fragment003.prefix')=='cff20d728df5f182c64617722b2fb26c04827a27cd8e36e8d6da53b2f1ca96b6' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment003.prefix')=='cff20d728df5f182c64617722b2fb26c04827a27cd8e36e8d6da53b2f1ca96b6','fragment pin fragment003.prefix')
need(sha(P/'src/DiophantineConsistency/fragment004.prefix')=='b5626abd6530966f3fecbfa123e387eebc93d08bd7796830c51a86ec1df1f4f4' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment004.prefix')=='b5626abd6530966f3fecbfa123e387eebc93d08bd7796830c51a86ec1df1f4f4','fragment pin fragment004.prefix')
need(sha(P/'src/DiophantineConsistency/fragment005.prefix')=='e16d12e82365480b7d0071745e9f8add4658cb25919c8bebfc0af8b4fdd632f5' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment005.prefix')=='e16d12e82365480b7d0071745e9f8add4658cb25919c8bebfc0af8b4fdd632f5','fragment pin fragment005.prefix')
need(sha(P/'src/DiophantineConsistency/fragment006.prefix')=='281040483af95b930c1cf204be9f5ea8245c27d347cc629dbbabcfde96277560' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment006.prefix')=='281040483af95b930c1cf204be9f5ea8245c27d347cc629dbbabcfde96277560','fragment pin fragment006.prefix')
need(sha(P/'src/DiophantineConsistency/fragment007.prefix')=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment007.prefix')=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb','fragment pin fragment007.prefix')
need(sha(P/'src/DiophantineConsistency/fragment008.prefix')=='1cfa9eeb3c2282145af1a15790ab5b154c3cf3ac45bf0897ddf0d8c39ec6cead' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment008.prefix')=='1cfa9eeb3c2282145af1a15790ab5b154c3cf3ac45bf0897ddf0d8c39ec6cead','fragment pin fragment008.prefix')
need(sha(P/'src/DiophantineConsistency/fragment009.prefix')=='baddcc15ca40b470fde46c336eb437a23e128a25255b1fda4eb3ac4ed7cbfa00' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment009.prefix')=='baddcc15ca40b470fde46c336eb437a23e128a25255b1fda4eb3ac4ed7cbfa00','fragment pin fragment009.prefix')
need(sha(P/'src/DiophantineConsistency/fragment010.prefix')=='e89262c21d71337bea84114fe980a2ae9cf9c67d4a6fe5c8fb5940e6f1d23116' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment010.prefix')=='e89262c21d71337bea84114fe980a2ae9cf9c67d4a6fe5c8fb5940e6f1d23116','fragment pin fragment010.prefix')
need(sha(P/'src/DiophantineConsistency/fragment011.prefix')=='30222de1c78c69326856e466aa3046ead9db68c6e90e31777d885fd137b08a9a' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment011.prefix')=='30222de1c78c69326856e466aa3046ead9db68c6e90e31777d885fd137b08a9a','fragment pin fragment011.prefix')
need(sha(P/'src/DiophantineConsistency/fragment012.prefix')=='78003334a7103d06878b53a849b800a4e0607df1a6a745e08626c29f72369de5' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment012.prefix')=='78003334a7103d06878b53a849b800a4e0607df1a6a745e08626c29f72369de5','fragment pin fragment012.prefix')
need(sha(P/'src/DiophantineConsistency/fragment013.prefix')=='5c8b0831c004a6142efb5344a013f93b0d916f2f9e7b590b11827a1064b6ea2b' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment013.prefix')=='5c8b0831c004a6142efb5344a013f93b0d916f2f9e7b590b11827a1064b6ea2b','fragment pin fragment013.prefix')
need(sha(P/'src/DiophantineConsistency/fragment014.prefix')=='04a54dbadac542f4378ce65a42e1998d4446e2ecf17b69191c7a397ccb306213' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment014.prefix')=='04a54dbadac542f4378ce65a42e1998d4446e2ecf17b69191c7a397ccb306213','fragment pin fragment014.prefix')
need(sha(P/'src/DiophantineConsistency/fragment015.prefix')=='1f74586ff5211bde8f75c6efea79032ef94d362b76018e4ff3f215b10d0c1011' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment015.prefix')=='1f74586ff5211bde8f75c6efea79032ef94d362b76018e4ff3f215b10d0c1011','fragment pin fragment015.prefix')
need(sha(P/'src/DiophantineConsistency/fragment016.prefix')=='5c25cdef8723f63a3e7d14edbe4c0ba3e277c626ff080be98e6bac08aa400717' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment016.prefix')=='5c25cdef8723f63a3e7d14edbe4c0ba3e277c626ff080be98e6bac08aa400717','fragment pin fragment016.prefix')
need(sha(P/'src/DiophantineConsistency/fragment017.prefix')=='6b1334ee2031c683a48cfe7e0202ab97bc48d6f31e9081a367f0d4c189246a07' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment017.prefix')=='6b1334ee2031c683a48cfe7e0202ab97bc48d6f31e9081a367f0d4c189246a07','fragment pin fragment017.prefix')
need(sha(P/'src/DiophantineConsistency/fragment018.prefix')=='25c79c828c30818e813300b3a49a51ee885382ec1443876618d769c134869d47' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment018.prefix')=='25c79c828c30818e813300b3a49a51ee885382ec1443876618d769c134869d47','fragment pin fragment018.prefix')
need(sha(P/'src/DiophantineConsistency/fragment019.prefix')=='4b227777d4dd1fc61c6f884f48641d02b4d121d3fd328cb08b5531fcacdabf8a' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment019.prefix')=='4b227777d4dd1fc61c6f884f48641d02b4d121d3fd328cb08b5531fcacdabf8a','fragment pin fragment019.prefix')
need(sha(P/'src/DiophantineConsistency/fragment020.prefix')=='4e07408562bedb8b60ce05c1decfe3ad16b72230967de01f640b7e4729b49fce' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment020.prefix')=='4e07408562bedb8b60ce05c1decfe3ad16b72230967de01f640b7e4729b49fce','fragment pin fragment020.prefix')
need(sha(P/'src/DiophantineConsistency/fragment021.prefix')=='39c0895e8a48b2e6af48d3bab4e157e3d1ac276f2abb726e68c3280652b5b717' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment021.prefix')=='39c0895e8a48b2e6af48d3bab4e157e3d1ac276f2abb726e68c3280652b5b717','fragment pin fragment021.prefix')
need(sha(P/'src/DiophantineConsistency/fragment022.prefix')=='a04522ce19bacf74c2a52bf26efe1986d7685cfb8efc7b4aaedecae8baa6793e' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment022.prefix')=='a04522ce19bacf74c2a52bf26efe1986d7685cfb8efc7b4aaedecae8baa6793e','fragment pin fragment022.prefix')
need(sha(P/'src/DiophantineConsistency/fragment023.prefix')=='d4735e3a265e16eee03f59718b9b5d03019c07d8b6c51f90da3a666eec13ab35' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment023.prefix')=='d4735e3a265e16eee03f59718b9b5d03019c07d8b6c51f90da3a666eec13ab35','fragment pin fragment023.prefix')
need(sha(P/'src/DiophantineConsistency/fragment024.prefix')=='0afe0e77d90ef135879cc0f863c4cf74db7372150240757e37d44c8b012da931' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment024.prefix')=='0afe0e77d90ef135879cc0f863c4cf74db7372150240757e37d44c8b012da931','fragment pin fragment024.prefix')
need(sha(P/'src/DiophantineConsistency/fragment025.prefix')=='6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment025.prefix')=='6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b','fragment pin fragment025.prefix')
need(sha(P/'src/DiophantineConsistency/fragment026.prefix')=='c033b26d2e2cdc4d41d0249cf8eb4e82a715398162ef47d6b1b678fd2b205b2a' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment026.prefix')=='c033b26d2e2cdc4d41d0249cf8eb4e82a715398162ef47d6b1b678fd2b205b2a','fragment pin fragment026.prefix')
need(sha(P/'src/DiophantineConsistency/fragment027.prefix')=='bb60c5d0a88a11416f988b45ae42f9d9a4d9f25e51a721aaaba44c8a3b45c621' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment027.prefix')=='bb60c5d0a88a11416f988b45ae42f9d9a4d9f25e51a721aaaba44c8a3b45c621','fragment pin fragment027.prefix')
need(sha(P/'src/DiophantineConsistency/fragment028.prefix')=='7ee7e25311863d02e6ae720fdca22a647b5f0fae792d39290a8588d245878496' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment028.prefix')=='7ee7e25311863d02e6ae720fdca22a647b5f0fae792d39290a8588d245878496','fragment pin fragment028.prefix')
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='06256df1f94947b245672c19a3cc2830e36023e24477a52264b7d521423b30df','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==14 and base['rows'][13]['module']=='Sign14PrefixCodeRow04','bridge state')
need(sha(D/'research/nine-sharing-sign14-prefix-code-check/attempt01/outer-result.json')=='1e6462f892a7dd14d86f7e8797cfc40db6984c0ef6fb59541f9a0f7bd2b44805','bridge outer record')
need(sha(D/'reviews/nine-sharing-sign14-prefix-code-terminal-independent/check.py')=='1c9fee1fce741db0a3de137518bb7221328a52dc5698d90e5fa90659c86eb37c','bridge terminal audit checker')
need(json.loads((D/'research/nine-sharing-sign14-prefix-code-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==0,'bridge outer status')
need(sha(P/'source-manifest.json')=='6324e437e9de7b54f2c9302801ff4a638c76431da371f45e93a6f2b1efa2ca5d','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'bridge stage '+n);need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'bridge source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'bridge log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'bridge unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'bridge guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'bridge overlay '+k)

for n in ('Sign14PrefixDagFragments00','Sign14PrefixDagFragments01','Sign14PrefixDagFragments02','Sign14PrefixDagFragments03','Sign14PrefixDagFragments04','Sign14PrefixDagFragments05','Sign14PrefixDagShared00','Sign14PrefixDagShared01','Sign14PrefixDagShared02','Sign14PrefixDagShared03','Sign14PrefixDagShared04','Sign14PrefixDagShared05','Sign14PrefixDagShared06','Sign14PrefixDagShared07','Sign14PrefixDagShared08','Sign14PrefixDagRow00','Sign14PrefixDagRow01','Sign14PrefixDagRow02','Sign14PrefixDagRow03','Sign14PrefixDagRow04',):need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'candidate target collision '+n)
for e in entries:
 src=P/'src/DiophantineConsistency'/(e['module'].split('.')[-1]+'.lean');need(sha(src)==e['source_sha256'],'source pin '+e['module'])
 need(sha(REPO/e['source'])==e['source_sha256'],'source original '+e['module'])
# Verify declared dependencies of stages are topologically ordered.
seen=set()
for entry in entries:
 for dep in entry['imports']:
  if dep in [x['module'] for x in entries]:need(dep in seen,'non-topological '+dep)
 seen.add(entry['module'])
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stage_count':len(entries),'scope':'Source/provider point checks only; no Lean, complete transitive trace or model proof.'},sort_keys=True));raise SystemExit(0)
need(not sys.argv[1:],'unexpected arguments')
for proc in Path('/proc').iterdir():
 if not proc.name.isdecimal():continue
 try:need(not ((proc/'comm').read_text().strip()=='lean' and (proc/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X')),'another Lean process is active')
 except (FileNotFoundError,ProcessLookupError):continue
need(shutil.disk_usage('/tmp').free>=5_000_000_000 and int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024>=10*1024**3,'resources')
spec=importlib.util.spec_from_file_location('monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
OUT.mkdir();(OUT/'src/DiophantineConsistency').mkdir(parents=True);(OUT/'lib/DiophantineConsistency').mkdir(parents=True)
links={}
for k,v in base['overlay_links'].items():
 rel=Path(k).relative_to(BASE/'lib');q=OUT/'lib'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(v);links[str(q)]=v
for row in base['rows']:
 n=row['module'];q=OUT/'lib/DiophantineConsistency'/(n+'.olean');q.symlink_to((BASE/'lib/DiophantineConsistency'/(n+'.olean')).resolve());links[str(q)]=str(q.resolve())
for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))
shutil.copyfile(P/'src/DiophantineConsistency/fragment000.prefix',OUT/'src/DiophantineConsistency/fragment000.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment001.prefix',OUT/'src/DiophantineConsistency/fragment001.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment002.prefix',OUT/'src/DiophantineConsistency/fragment002.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment003.prefix',OUT/'src/DiophantineConsistency/fragment003.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment004.prefix',OUT/'src/DiophantineConsistency/fragment004.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment005.prefix',OUT/'src/DiophantineConsistency/fragment005.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment006.prefix',OUT/'src/DiophantineConsistency/fragment006.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment007.prefix',OUT/'src/DiophantineConsistency/fragment007.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment008.prefix',OUT/'src/DiophantineConsistency/fragment008.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment009.prefix',OUT/'src/DiophantineConsistency/fragment009.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment010.prefix',OUT/'src/DiophantineConsistency/fragment010.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment011.prefix',OUT/'src/DiophantineConsistency/fragment011.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment012.prefix',OUT/'src/DiophantineConsistency/fragment012.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment013.prefix',OUT/'src/DiophantineConsistency/fragment013.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment014.prefix',OUT/'src/DiophantineConsistency/fragment014.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment015.prefix',OUT/'src/DiophantineConsistency/fragment015.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment016.prefix',OUT/'src/DiophantineConsistency/fragment016.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment017.prefix',OUT/'src/DiophantineConsistency/fragment017.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment018.prefix',OUT/'src/DiophantineConsistency/fragment018.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment019.prefix',OUT/'src/DiophantineConsistency/fragment019.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment020.prefix',OUT/'src/DiophantineConsistency/fragment020.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment021.prefix',OUT/'src/DiophantineConsistency/fragment021.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment022.prefix',OUT/'src/DiophantineConsistency/fragment022.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment023.prefix',OUT/'src/DiophantineConsistency/fragment023.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment024.prefix',OUT/'src/DiophantineConsistency/fragment024.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment025.prefix',OUT/'src/DiophantineConsistency/fragment025.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment026.prefix',OUT/'src/DiophantineConsistency/fragment026.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment027.prefix',OUT/'src/DiophantineConsistency/fragment027.prefix')
shutil.copyfile(P/'src/DiophantineConsistency/fragment028.prefix',OUT/'src/DiophantineConsistency/fragment028.prefix')
state={'status':'RUNNING','scope':'Bounded sign14 compositional fragment DAG encoding on captured Jones provider; no new base rebuild, no project-wide dependency load trace; endpoint outcome depends on stage results. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
try:
 env=dict(os.environ,LEAN_PATH=':'.join(map(str,roots[:-1])),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 for n,pin,entry in zip(names,pins,entries):
  src=OUT/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==pin,'snapshot drift '+n)
  imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M);need(imports==entry['imports'],'source imports '+n);prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M3600','-j1','-DElab.async=false'];row={'module':n,'source_sha256':pin};state['rows'].append(row);save()
  log=OUT/(n+'-deps.txt');res=monitor.run(prefix+['--deps',str(src)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['deps']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'deps failed '+n)
  deps={};counts={}
  for line in log.read_text().splitlines():
   p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dep '+line);mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in deps or (mod=='Init' and counts[mod]<=2 and deps[mod]['path']==line),'duplicate '+mod);deps[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
  need(set(deps)-{'Init'}==set(imports)-{'Init'},'dependency set '+n)
  for mod,rec in deps.items():
   candidates=[r/(mod.replace('.','/')+'.olean') for r in roots if (r/(mod.replace('.','/')+'.olean')).is_file()];need(candidates and str(candidates[0])==rec['path'],'dependency route '+mod)
  row['dependencies']=deps;row['direct_guard']=guard(deps)
  for mod in imports:
   dep=deps[mod];obs=row['direct_guard'].get(dep['path']);local=mod.split('.')[-1]
   if local=='Sign14PrefixCodeRow04':expected_hash=base['rows'][13]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign14PrefixCodeRow04.olean'
   elif local in ('Sign14PrefixDagFragments00','Sign14PrefixDagFragments01','Sign14PrefixDagFragments02','Sign14PrefixDagFragments03','Sign14PrefixDagFragments04','Sign14PrefixDagFragments05','Sign14PrefixDagShared00','Sign14PrefixDagShared01','Sign14PrefixDagShared02','Sign14PrefixDagShared03','Sign14PrefixDagShared04','Sign14PrefixDagShared05','Sign14PrefixDagShared06','Sign14PrefixDagShared07','Sign14PrefixDagShared08','Sign14PrefixDagRow00','Sign14PrefixDagRow01','Sign14PrefixDagRow02','Sign14PrefixDagRow03'):
    prior=[r for r in state['rows'][:-1] if r['module']==local];need(len(prior)==1,'local producer '+local);expected_hash=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(local+'.olean')
   elif local in framework['observed']:
    rec=framework['observed'][local];expected_hash=rec['sha256'];path=Path(rec['realpath'])
   else:need(False,'unexpected import '+mod)
   need(dep['sha256']==expected_hash and dep['realpath']==str(path.resolve()) and obs is not None and obs['sha256']==dep['sha256'] and obs['realpath']==dep['realpath'],'direct producer binding '+mod)
  save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean');res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n);need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(P/'src/DiophantineConsistency'/(row['module']+'.lean'))==entry['source_sha256'] and sha(REPO/entry['source'])==entry['source_sha256'],'final source drift '+row['module'])
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final provider drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay drift '+k)
 check_external_syntax()
 need(sha(P/'src/DiophantineConsistency/fragment000.prefix')=='118dce858ad9198efce02acfa71b64f0729ea1da75619140aafd575baeaed053' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment000.prefix')=='118dce858ad9198efce02acfa71b64f0729ea1da75619140aafd575baeaed053' and sha(OUT/'src/DiophantineConsistency/fragment000.prefix')=='118dce858ad9198efce02acfa71b64f0729ea1da75619140aafd575baeaed053','fragment drift fragment000.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment001.prefix')=='5f19afc99d0b65bd9f6dbc8eb629875f34f474f8d24868bce56635a11caeac49' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment001.prefix')=='5f19afc99d0b65bd9f6dbc8eb629875f34f474f8d24868bce56635a11caeac49' and sha(OUT/'src/DiophantineConsistency/fragment001.prefix')=='5f19afc99d0b65bd9f6dbc8eb629875f34f474f8d24868bce56635a11caeac49','fragment drift fragment001.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment002.prefix')=='5cc4a464b94e50c4e73286aa3a36b6218c7e27ad3b548ab7ae782aa1252ad820' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment002.prefix')=='5cc4a464b94e50c4e73286aa3a36b6218c7e27ad3b548ab7ae782aa1252ad820' and sha(OUT/'src/DiophantineConsistency/fragment002.prefix')=='5cc4a464b94e50c4e73286aa3a36b6218c7e27ad3b548ab7ae782aa1252ad820','fragment drift fragment002.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment003.prefix')=='cff20d728df5f182c64617722b2fb26c04827a27cd8e36e8d6da53b2f1ca96b6' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment003.prefix')=='cff20d728df5f182c64617722b2fb26c04827a27cd8e36e8d6da53b2f1ca96b6' and sha(OUT/'src/DiophantineConsistency/fragment003.prefix')=='cff20d728df5f182c64617722b2fb26c04827a27cd8e36e8d6da53b2f1ca96b6','fragment drift fragment003.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment004.prefix')=='b5626abd6530966f3fecbfa123e387eebc93d08bd7796830c51a86ec1df1f4f4' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment004.prefix')=='b5626abd6530966f3fecbfa123e387eebc93d08bd7796830c51a86ec1df1f4f4' and sha(OUT/'src/DiophantineConsistency/fragment004.prefix')=='b5626abd6530966f3fecbfa123e387eebc93d08bd7796830c51a86ec1df1f4f4','fragment drift fragment004.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment005.prefix')=='e16d12e82365480b7d0071745e9f8add4658cb25919c8bebfc0af8b4fdd632f5' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment005.prefix')=='e16d12e82365480b7d0071745e9f8add4658cb25919c8bebfc0af8b4fdd632f5' and sha(OUT/'src/DiophantineConsistency/fragment005.prefix')=='e16d12e82365480b7d0071745e9f8add4658cb25919c8bebfc0af8b4fdd632f5','fragment drift fragment005.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment006.prefix')=='281040483af95b930c1cf204be9f5ea8245c27d347cc629dbbabcfde96277560' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment006.prefix')=='281040483af95b930c1cf204be9f5ea8245c27d347cc629dbbabcfde96277560' and sha(OUT/'src/DiophantineConsistency/fragment006.prefix')=='281040483af95b930c1cf204be9f5ea8245c27d347cc629dbbabcfde96277560','fragment drift fragment006.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment007.prefix')=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment007.prefix')=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb' and sha(OUT/'src/DiophantineConsistency/fragment007.prefix')=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb','fragment drift fragment007.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment008.prefix')=='1cfa9eeb3c2282145af1a15790ab5b154c3cf3ac45bf0897ddf0d8c39ec6cead' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment008.prefix')=='1cfa9eeb3c2282145af1a15790ab5b154c3cf3ac45bf0897ddf0d8c39ec6cead' and sha(OUT/'src/DiophantineConsistency/fragment008.prefix')=='1cfa9eeb3c2282145af1a15790ab5b154c3cf3ac45bf0897ddf0d8c39ec6cead','fragment drift fragment008.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment009.prefix')=='baddcc15ca40b470fde46c336eb437a23e128a25255b1fda4eb3ac4ed7cbfa00' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment009.prefix')=='baddcc15ca40b470fde46c336eb437a23e128a25255b1fda4eb3ac4ed7cbfa00' and sha(OUT/'src/DiophantineConsistency/fragment009.prefix')=='baddcc15ca40b470fde46c336eb437a23e128a25255b1fda4eb3ac4ed7cbfa00','fragment drift fragment009.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment010.prefix')=='e89262c21d71337bea84114fe980a2ae9cf9c67d4a6fe5c8fb5940e6f1d23116' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment010.prefix')=='e89262c21d71337bea84114fe980a2ae9cf9c67d4a6fe5c8fb5940e6f1d23116' and sha(OUT/'src/DiophantineConsistency/fragment010.prefix')=='e89262c21d71337bea84114fe980a2ae9cf9c67d4a6fe5c8fb5940e6f1d23116','fragment drift fragment010.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment011.prefix')=='30222de1c78c69326856e466aa3046ead9db68c6e90e31777d885fd137b08a9a' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment011.prefix')=='30222de1c78c69326856e466aa3046ead9db68c6e90e31777d885fd137b08a9a' and sha(OUT/'src/DiophantineConsistency/fragment011.prefix')=='30222de1c78c69326856e466aa3046ead9db68c6e90e31777d885fd137b08a9a','fragment drift fragment011.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment012.prefix')=='78003334a7103d06878b53a849b800a4e0607df1a6a745e08626c29f72369de5' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment012.prefix')=='78003334a7103d06878b53a849b800a4e0607df1a6a745e08626c29f72369de5' and sha(OUT/'src/DiophantineConsistency/fragment012.prefix')=='78003334a7103d06878b53a849b800a4e0607df1a6a745e08626c29f72369de5','fragment drift fragment012.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment013.prefix')=='5c8b0831c004a6142efb5344a013f93b0d916f2f9e7b590b11827a1064b6ea2b' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment013.prefix')=='5c8b0831c004a6142efb5344a013f93b0d916f2f9e7b590b11827a1064b6ea2b' and sha(OUT/'src/DiophantineConsistency/fragment013.prefix')=='5c8b0831c004a6142efb5344a013f93b0d916f2f9e7b590b11827a1064b6ea2b','fragment drift fragment013.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment014.prefix')=='04a54dbadac542f4378ce65a42e1998d4446e2ecf17b69191c7a397ccb306213' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment014.prefix')=='04a54dbadac542f4378ce65a42e1998d4446e2ecf17b69191c7a397ccb306213' and sha(OUT/'src/DiophantineConsistency/fragment014.prefix')=='04a54dbadac542f4378ce65a42e1998d4446e2ecf17b69191c7a397ccb306213','fragment drift fragment014.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment015.prefix')=='1f74586ff5211bde8f75c6efea79032ef94d362b76018e4ff3f215b10d0c1011' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment015.prefix')=='1f74586ff5211bde8f75c6efea79032ef94d362b76018e4ff3f215b10d0c1011' and sha(OUT/'src/DiophantineConsistency/fragment015.prefix')=='1f74586ff5211bde8f75c6efea79032ef94d362b76018e4ff3f215b10d0c1011','fragment drift fragment015.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment016.prefix')=='5c25cdef8723f63a3e7d14edbe4c0ba3e277c626ff080be98e6bac08aa400717' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment016.prefix')=='5c25cdef8723f63a3e7d14edbe4c0ba3e277c626ff080be98e6bac08aa400717' and sha(OUT/'src/DiophantineConsistency/fragment016.prefix')=='5c25cdef8723f63a3e7d14edbe4c0ba3e277c626ff080be98e6bac08aa400717','fragment drift fragment016.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment017.prefix')=='6b1334ee2031c683a48cfe7e0202ab97bc48d6f31e9081a367f0d4c189246a07' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment017.prefix')=='6b1334ee2031c683a48cfe7e0202ab97bc48d6f31e9081a367f0d4c189246a07' and sha(OUT/'src/DiophantineConsistency/fragment017.prefix')=='6b1334ee2031c683a48cfe7e0202ab97bc48d6f31e9081a367f0d4c189246a07','fragment drift fragment017.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment018.prefix')=='25c79c828c30818e813300b3a49a51ee885382ec1443876618d769c134869d47' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment018.prefix')=='25c79c828c30818e813300b3a49a51ee885382ec1443876618d769c134869d47' and sha(OUT/'src/DiophantineConsistency/fragment018.prefix')=='25c79c828c30818e813300b3a49a51ee885382ec1443876618d769c134869d47','fragment drift fragment018.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment019.prefix')=='4b227777d4dd1fc61c6f884f48641d02b4d121d3fd328cb08b5531fcacdabf8a' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment019.prefix')=='4b227777d4dd1fc61c6f884f48641d02b4d121d3fd328cb08b5531fcacdabf8a' and sha(OUT/'src/DiophantineConsistency/fragment019.prefix')=='4b227777d4dd1fc61c6f884f48641d02b4d121d3fd328cb08b5531fcacdabf8a','fragment drift fragment019.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment020.prefix')=='4e07408562bedb8b60ce05c1decfe3ad16b72230967de01f640b7e4729b49fce' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment020.prefix')=='4e07408562bedb8b60ce05c1decfe3ad16b72230967de01f640b7e4729b49fce' and sha(OUT/'src/DiophantineConsistency/fragment020.prefix')=='4e07408562bedb8b60ce05c1decfe3ad16b72230967de01f640b7e4729b49fce','fragment drift fragment020.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment021.prefix')=='39c0895e8a48b2e6af48d3bab4e157e3d1ac276f2abb726e68c3280652b5b717' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment021.prefix')=='39c0895e8a48b2e6af48d3bab4e157e3d1ac276f2abb726e68c3280652b5b717' and sha(OUT/'src/DiophantineConsistency/fragment021.prefix')=='39c0895e8a48b2e6af48d3bab4e157e3d1ac276f2abb726e68c3280652b5b717','fragment drift fragment021.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment022.prefix')=='a04522ce19bacf74c2a52bf26efe1986d7685cfb8efc7b4aaedecae8baa6793e' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment022.prefix')=='a04522ce19bacf74c2a52bf26efe1986d7685cfb8efc7b4aaedecae8baa6793e' and sha(OUT/'src/DiophantineConsistency/fragment022.prefix')=='a04522ce19bacf74c2a52bf26efe1986d7685cfb8efc7b4aaedecae8baa6793e','fragment drift fragment022.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment023.prefix')=='d4735e3a265e16eee03f59718b9b5d03019c07d8b6c51f90da3a666eec13ab35' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment023.prefix')=='d4735e3a265e16eee03f59718b9b5d03019c07d8b6c51f90da3a666eec13ab35' and sha(OUT/'src/DiophantineConsistency/fragment023.prefix')=='d4735e3a265e16eee03f59718b9b5d03019c07d8b6c51f90da3a666eec13ab35','fragment drift fragment023.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment024.prefix')=='0afe0e77d90ef135879cc0f863c4cf74db7372150240757e37d44c8b012da931' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment024.prefix')=='0afe0e77d90ef135879cc0f863c4cf74db7372150240757e37d44c8b012da931' and sha(OUT/'src/DiophantineConsistency/fragment024.prefix')=='0afe0e77d90ef135879cc0f863c4cf74db7372150240757e37d44c8b012da931','fragment drift fragment024.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment025.prefix')=='6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment025.prefix')=='6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b' and sha(OUT/'src/DiophantineConsistency/fragment025.prefix')=='6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b','fragment drift fragment025.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment026.prefix')=='c033b26d2e2cdc4d41d0249cf8eb4e82a715398162ef47d6b1b678fd2b205b2a' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment026.prefix')=='c033b26d2e2cdc4d41d0249cf8eb4e82a715398162ef47d6b1b678fd2b205b2a' and sha(OUT/'src/DiophantineConsistency/fragment026.prefix')=='c033b26d2e2cdc4d41d0249cf8eb4e82a715398162ef47d6b1b678fd2b205b2a','fragment drift fragment026.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment027.prefix')=='bb60c5d0a88a11416f988b45ae42f9d9a4d9f25e51a721aaaba44c8a3b45c621' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment027.prefix')=='bb60c5d0a88a11416f988b45ae42f9d9a4d9f25e51a721aaaba44c8a3b45c621' and sha(OUT/'src/DiophantineConsistency/fragment027.prefix')=='bb60c5d0a88a11416f988b45ae42f9d9a4d9f25e51a721aaaba44c8a3b45c621','fragment drift fragment027.prefix')
 need(sha(P/'src/DiophantineConsistency/fragment028.prefix')=='7ee7e25311863d02e6ae720fdca22a647b5f0fae792d39290a8588d245878496' and sha(D/'research/nine-sharing-sign14-prefix-dag-fragments/fragment028.prefix')=='7ee7e25311863d02e6ae720fdca22a647b5f0fae792d39290a8588d245878496' and sha(OUT/'src/DiophantineConsistency/fragment028.prefix')=='7ee7e25311863d02e6ae720fdca22a647b5f0fae792d39290a8588d245878496','fragment drift fragment028.prefix')
 state['status']='PASS';save();print('PASS sign14 compositional fragment DAG encoding')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
