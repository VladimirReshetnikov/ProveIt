#!/usr/bin/env python3
"""HELD: check trace75/direct-BFS support against the fresh replay union."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse,fcntl,json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];SRC=H/'Trace75BFSLocalWord.lean'
ATT=D/'research/trace75-fresh-provider-rebuild/observations/attempt01';RESULT=ATT/'result.json';INITIAL=ATT/'initial-union.json';OUTER=D/'research/trace75-fresh-provider-rebuild/observations/outer-attempt01/terminal.json'
BFSATT=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01';BFS=BFSATT/'result.json';OUTSIDE=BFSATT/'outside-baseline.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={SRC:'56a79783146f91246010e77d67618f4abee77fac833f29bbfb701e7eab31c6c5',RESULT:'b74858343a05be6710e0666abb86189aea375ebd4d494411fee00d31e9f31e1a',INITIAL:'1b6b3f1c3938bd1448dda5811509971de2b16d8c07a407831a86434b89863c10',OUTER:'4c310be9b2ee9aa32378f27869c87e7bbbd8af2512f3b6391d02518e3dcbc7af',BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',OUTSIDE:'5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777',HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}

PINS[D/'research/trace75-bfs-carry-prototype/observations/attempt01/result.json']='7704d80833c17b04cf345e269213121f4bbf41537b62262921f7177f21dd4bc7'
PINS[D/'research/trace75-bfs-carry-prototype/observations/outer-attempt01/terminal.json']='c12da16e2196705490b6b5c54bf1c626eb8bda5446772018974d2e88a7c84631'
PINS[D/'research/trace75-fresh-fixedslots-prototype/observations/attempt01/result.json']='7f1df5657b7a5a82e1136b9d2e19e067c57312c1bbc6ae23dc21e6946ce06873'
PINS[D/'research/trace75-fresh-fixedslots-prototype/observations/outer-attempt01/terminal.json']='4c78ac9fab5a3c8d5da0bbb191932180e0426deef1b9c818c66302990412b2d1'

PINS[D/'research/trace75-bfs-support-prototype/observations/attempt01/result.json']='656ef70f8acfe147effa3b3339b5f6a210c924ab5defe5caa10097faf3fcfeaa'
PINS[D/'research/trace75-bfs-support-prototype/observations/outer-attempt01/terminal.json']='db3489eec9ed11e229931ed331b970fdcecb9d2b83e9259f9928e71c5ab45b51'
PINS[D/'research/trace75-bfs-clean-carry-prototype/observations/attempt01/result.json']='c370158e10e44877025fdc28c0abf5040143a300cf7db8a8bbcc7c366e16b92a'
PINS[D/'research/trace75-bfs-clean-carry-prototype/observations/outer-attempt01/terminal.json']='ca17662a11a3aa67b5815590157fe88cf03072c0abd974f4aa274523e83420ea'
PINS[D/'research/trace75-bfs-simple-parity-prototype/observations/attempt01/result.json']='b02af2fb1a9610dc523c1d3e6582a680811bb0966fe6cdf463bddd5435d99b01'
PINS[D/'research/trace75-bfs-simple-parity-prototype/observations/outer-attempt01/terminal.json']='9cccfed92c8af9105c754b8e083f824903598e82ab9995742ab12a2e2e25252e'
PINS[D/'research/trace75-bfs-occupied-prototype/observations/attempt01/result.json']='ec5cb21bb0c36527ad05a4474d0b9a1cff598a504a6a2a2d4a754471b041d633'
PINS[D/'research/trace75-bfs-occupied-prototype/observations/outer-attempt01/terminal.json']='fe59f80dd0339adf513b65d763402c5977ec67afd2f4e4ce269f7e219c96baf1'
PINS[D/'research/trace75-bfs-aligned-shift-prototype/observations/attempt01/result.json']='76788e416a7ed045716de97e103d2346cdee29f306acfcbb49447e5a834d33da'
PINS[D/'research/trace75-bfs-aligned-shift-prototype/observations/outer-attempt01/terminal.json']='953c46e5cafe93266535b854948af27535999bdac7510c614f655561d7fa3f9f'
PINS[D/'research/trace75-bfs-cell-shift-prototype/observations/attempt01/result.json']='57660aa69e2ecde3b0e10c20f0edb01681f7774d04c80a1c1d7b06e081f7caa3'
PINS[D/'research/trace75-bfs-cell-shift-prototype/observations/outer-attempt01/terminal.json']='48bca5b09f8b1b8759bf2258bb5e21220d567b954d1220ca9644a09165f85944'
PINS[D/'research/trace75-bfs-uniform-reset-prototype/observations/attempt01/result.json']='252268f327d68dd2ff352a2229a54d053bc6fd324a0f2bf483f2e19a8861ac9f'
PINS[D/'research/trace75-bfs-uniform-reset-prototype/observations/outer-attempt01/terminal.json']='a4da339bb4e2527533e23a91b4624c1b51fc28b050592305a1704dfcc424ea07'
PINS[D/'research/trace75-bfs-uniform-decoder-prototype/observations/attempt01/result.json']='459c9d8576ce39bd96bdbfa4da34640d2e0705ce0ea03f46768695c8b4196c54'
PINS[D/'research/trace75-bfs-uniform-decoder-prototype/observations/outer-attempt01/terminal.json']='6e1ddc62d434c95e160648607e2e66133561fefabcb7fb365a5fd1fb57d7c25e'
PINS[D/'research/trace75-bfs-field-markers-prototype/observations/attempt01/result.json']='30bc3205b4bd21130e871e518c9360e04cb3db4918cc17b2bcfdb1dc8ed0f18b'
PINS[D/'research/trace75-bfs-field-markers-prototype/observations/outer-attempt01/terminal.json']='b876e772806063052002332cf1c2572e0c2896da60d44e36a7e32539dedc4695'
PINS[D/'research/trace75-bfs-spatial-successor-prototype/observations/attempt01/result.json']='24c98a5979883eaa56cbf7992de814fd3eb6b33dd7b8daa156bf08af870ddd7b'
PINS[D/'research/trace75-bfs-spatial-successor-prototype/observations/outer-attempt01/terminal.json']='eaa49e8dbfb20e32fa5b56b39a361dd7622f33ba5772e69cbf16640488221f28'
PINS[D/'research/trace75-bfs-all-blocks-prototype/observations/attempt01/result.json']='9f4f627f52e667075b6b025b2b99b6e24920f72b74169e54b3f2e2a2dee4a6b2'
PINS[D/'research/trace75-bfs-all-blocks-prototype/observations/outer-attempt01/terminal.json']='9fac2b6f25ded83af8d23bf78b85634670d41a636d21c31c568235b0a036ac3f'
PINS[D/'research/trace75-bfs-all-block-word-prototype/observations/attempt01/result.json']='46d8ffd2a89c1e7a955e54f763668bf0d03b2bb24aeea495b3a9bc6094756932'
PINS[D/'research/trace75-bfs-all-block-word-prototype/observations/outer-attempt01/terminal.json']='638abb41f85ec52f6cca75cf37d3988c761b5b024ecb11e85043a5d01ac47611'
PINS[D/'research/trace75-bfs-tile-match-prototype/observations/attempt01/result.json']='ad342d9ab25c03b26a6e9044c7f10675a482d026a85b043c149cce2bb725cb62'
PINS[D/'research/trace75-bfs-tile-match-prototype/observations/outer-attempt01/terminal.json']='f5d2c1c0a6274f1fc061d1426e1ea59e01e08abc3b5685039fb4ff199b396a30'
PINS[D/'research/trace75-bfs-field-cast-bridge-prototype/observations/attempt01/result.json']='a844c52fefb362b2ac6f6d97a328c270610e321b1d70723560a9c7a29dab52a8'
PINS[D/'research/trace75-bfs-field-cast-bridge-prototype/observations/outer-attempt01/terminal.json']='f7f791d26e7049aa3a5cfb9894df72d85f03c4c586bd36a240e18e4f41370a4e'
PINS[D/'research/trace75-bfs-anchored-match-prototype/observations/attempt01/result.json']='d5b24e81cb47a2079e576e043166e9a8ba8f2bcf2f87e9ffb73883203c0e36fa'
PINS[D/'research/trace75-bfs-anchored-match-prototype/observations/outer-attempt01/terminal.json']='fcd3dcdc47a545bce114634ac29d2db81b431b045efa172be385a6c9fe864d7e'
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def rel(n):
 need(re.fullmatch(r'[A-Za-z0-9_\.]+',n) is not None,'bad module '+n);return n.replace('.','/')
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),'dangling/non-file '+str(p));return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(stem):return {s:rec(Path(str(stem)+s)) for s in SUFFIXES}
def hashes(r):return {s:None if r[s] is None else r[s]['sha256'] for s in SUFFIXES}
def selected(n,roots):
 for root in roots:
  p=root/(rel(n)+'.olean')
  if os.path.lexists(p):need(p.is_file(),'dangling shadow '+str(p));return p
 return None
def report_ok(out,err):
 return out=="'Trace75BFSLocalWord.field_cast' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75BFSLocalWord.graph_local_word' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and err==''
def check_root(root,allowed):
 for p in root.rglob('*'):
  if p.is_symlink():need(p.is_file(),'dangling output-root entry '+str(p))
  if p.is_file() or p.is_symlink():need(str(p.relative_to(root)) in allowed,'unexpected output-root entry '+str(p))
def check_clients(clients):
 for directory,name,source_hash,object_hash in clients:
  need(directory.is_dir() and not directory.is_symlink() and directory.resolve(strict=True)==directory.absolute(),'client directory target drift '+name)
  check_root(directory,{name+'.lean',name+'.olean'})
  for suffix in ('.lean','.olean'):
   path=directory/(name+suffix);need(path.is_file() and not path.is_symlink() and path.resolve(strict=True)==path.absolute(),'client regular-file target drift '+str(path))
  need(sha(directory/(name+'.lean'))==source_hash and sha(directory/(name+'.olean'))==object_hash,'client root drift '+name)
  for suffix in SUFFIXES:
   if suffix!='.olean':need(not os.path.lexists(directory/(name+suffix)),'client companion appeared '+name+suffix)
def resources():
 rows=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in rows if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def guard():
 x=resources();need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<2,'resource preflight');return x
def monitored(cmd,env,out,err,timeout):
 pre=guard();samples=[];reason=None;start=time.monotonic()
 with out.open('x') as so,err.open('x') as se:
  proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
  try:
   while proc.poll() is None:
    time.sleep(1);s=resources();samples.append(s)
    if s['mem_available_kib']<8*1024**2 or len(s['lean'])>2:reason='resource guard';proc.kill();break
    if time.monotonic()-start>timeout:reason='timeout';proc.kill();break
  finally:
   if proc.poll() is None:proc.kill()
   proc.wait()
 return {'command':cmd,'env':env,'exit':proc.returncode,'reason':reason,'preflight':pre,'postflight':resources(),'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
def parse_header(text,path):
 lines=text.splitlines();need(lines and lines[0]=='BEGIN '+str(path) and lines[-1]=='END','bad header envelope')
 need(all(s.startswith('IMPORT ') and re.fullmatch(r'[A-Za-z0-9_\.]+',s[7:]) for s in lines[1:-1]),'bad header record');return [s[7:] for s in lines[1:-1]]
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args();need(args.preflight_only != bool(args.attempt),'choose preflight or attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
RUNSHA=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
run=json.loads(RESULT.read_text());outer=json.loads(OUTER.read_text());bfs=json.loads(BFS.read_text());outside=json.loads(OUTSIDE.read_text());initial=json.loads(INITIAL.read_text())
need(run['status']=='PASS' and outer['exit']==0 and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after'] and outer['child_result_sha256']==PINS[RESULT] and bfs['status']=='PASS','bad producer receipt')
for packet in ('trace75-bfs-carry-prototype','trace75-fresh-fixedslots-prototype','trace75-bfs-support-prototype','trace75-bfs-clean-carry-prototype','trace75-bfs-simple-parity-prototype','trace75-bfs-occupied-prototype','trace75-bfs-aligned-shift-prototype','trace75-bfs-cell-shift-prototype','trace75-bfs-uniform-reset-prototype','trace75-bfs-uniform-decoder-prototype','trace75-bfs-field-markers-prototype','trace75-bfs-spatial-successor-prototype','trace75-bfs-all-blocks-prototype','trace75-bfs-all-block-word-prototype','trace75-bfs-tile-match-prototype','trace75-bfs-field-cast-bridge-prototype','trace75-bfs-anchored-match-prototype'):
 c=D/'research'/packet/'observations/attempt01/result.json';o=D/'research'/packet/'observations/outer-attempt01/terminal.json';cr=json.loads(c.read_text());co=json.loads(o.read_text())
 need(cr['status']=='PASS' and co['exit']==0 and co['inputs_before']==co['inputs_after'] and co['wrapper_sha256_before']==co['wrapper_sha256_after'] and co['child_result_sha256']==sha(c),'bad client producer '+packet)
lib=Path(run['output_root'])/'lib';expected=dict(initial)
for st in run['stages']:
 need(st['status']=='PASS' and st['exit']==0 and st['reason'] is None,'stage failed');need(st['module'] not in expected,'duplicate stage');expected[st['module']]=st['object']
need(len(expected)==1977 and len(outside)==80,'inventory count')
source_imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',SRC.read_text(),re.M)
DIRECT=['Trace75BFSFieldCastBridge','Trace75BFSTileMatch','Trace75BFSAnchor','DiophantineConsistency.CompactLocalWord'];need(source_imports==DIRECT,'source imports changed')
prior=bfs['closure']['project'];ext=bfs['closure']['outside'];subtrees={}
for root in ['DiophantineConsistency.CompactLocalWord']:
 todo=deque([root]);seen=set();boundary=set()
 while todo:
  n=todo.popleft()
  if n in seen or n in boundary:continue
  if n not in prior:boundary.add(n);continue
  seen.add(n);todo.extend(prior[n]['imports'])
 need(boundary<=set(ext),'BFS subtree outside missing '+root);subtrees[root]={'project':sorted(seen),'outside':sorted(boundary)}
for root,sub in subtrees.items():
 for n in sub['project']:
  need(n in expected and hashes(expected[n])==hashes(prior[n]['companions']),'BFS ancestry/companion conflict '+n)
 for n in sub['outside']:need(n in outside and hashes(outside[n])==hashes(ext[n]['companions']),'BFS outside conflict '+n)
for n in ['DiophantineConsistency.CompactLocalWord']:need(n in expected,'direct provider absent '+n)
for n in ['Trace75BFSFieldCastBridge','Trace75BFSTileMatch','Trace75BFSAnchor']:need(n not in expected,'client unexpectedly in union '+n)
CASTROOT=Path('/tmp/trace75-bfs-fieldcast-7s_1mnoi');ANCHORROOT=Path('/tmp/trace75-bfs-anchor-1oa2aaqs');TILEROOT=Path('/tmp/trace75-bfs-tilematch-spgmvnyq');WORDROOT=Path('/tmp/trace75-bfs-allblockword-_c_e6kmb');BLOCKSROOT=Path('/tmp/trace75-bfs-allblocks-9b9tohp3');SPATIALROOT=Path('/tmp/trace75-bfs-spatialsuccessor-fl5a4a7i');DECODEROOT=Path('/tmp/trace75-bfs-uniformdecoder-8n6ji92i');FIELDROOT=Path('/tmp/trace75-bfs-fieldmarkers-kx2zjp49');RESETROOT=Path('/tmp/trace75-bfs-uniformreset-lqxlaw0u');CELLROOT=Path('/tmp/trace75-bfs-cellshift-9_fgrs9i');ALIGNROOT=Path('/tmp/trace75-bfs-alignedshift-64rdplmm');PARITYROOT=Path('/tmp/trace75-bfs-simpleparity-klgreprj');OCCUPIEDROOT=Path('/tmp/trace75-bfs-occupied-9u380_i0');CLEANROOT=Path('/tmp/trace75-bfs-cleancarry-t_64ksab');SUPPORTROOT=Path('/tmp/trace75-bfs-support-30d128xr');CARRYROOT=Path('/tmp/trace75-bfs-carry-fcp4lu0b');SLOTROOT=Path('/tmp/trace75-fresh-fixedslots-oyfhiba0')
CLIENTS=[(CASTROOT,'Trace75BFSFieldCastBridge','4138565a914e74ae8448f1f717296f34e0ef973a05ef28dc131b1c6f64b2a58d','5bdf2b8dce3c1dbbce5f62efc55a9d87df87e273ce4c985dac81d230e356aff2'),(ANCHORROOT,'Trace75BFSAnchor','14909b8f7730014230ef45f634ea0c26d835659174fe05233e7c5f366ac8248c','f0e250ac98bc56fa5ff8b48518df7eae2206f43a1548dd8cfc1d6f91b92bf099'),(TILEROOT,'Trace75BFSTileMatch','a1a20e4cf3e29818eff33b5e80bdfc0b903f55cf38af5cd6697a0cb0da9d8526','0043419a5d27dfeea59e0583718c1d105b5d860cfb77f846d9ce7a1ce93355b2'),(WORDROOT,'Trace75BFSAllBlockWord','d2157679d53263ce59e7cf094830f6c8ba577135ebdd2e9c650a3d88e63f7c23','ad6eda0a5c1a390493a943e97d08e84dc0eed993918d16122d0c0b3bebbfa23a'),(BLOCKSROOT,'Trace75BFSAllBlocks','dcd2412213b8cfc66f39834cde2f5e7421dc526191eeea7bd015cb27018f4259','4e8944a240915156fafabb828f2fcdca76393bf3a895532e19f36b90a02a1a5f'),(SPATIALROOT,'Trace75BFSSpatialSuccessor','d3b6373004b16f7c4c1517e8f2f4289760ce9df2c841b028acb072c98ffb000b','d028374852aed078f8c1a54c660787999bfbca195fac66278a73ed293f7e28af'),(DECODEROOT,'Trace75BFSUniformDecoder','ff8f6fb090a3140972795471be57fe5438abf6058ce49119d0d179cf95b73b06','f2ca7b64f92f89f3f95b8d381c4d7f509d137a490f819bb84b0f37906cd6603f'),(FIELDROOT,'Trace75BFSFieldMarkers','3c52b846ca5faffcd8cd97e69bd796277da73b40b0f8b1f5ae6cf5e3d91ff5ba','70c92a5033178fa7b102ef545bc9ba24b3e9addd2ca161930108ec10641a1ea4'),(RESETROOT,'Trace75BFSUniformReset','99d0a2dc08e267ed1e6cb25038fef47c6476024bb6a2b62107e0b1c263849e55','1c99b1ac2130c05c832de7041c7bed41562daf056faeaaa5220e5cc92eeeb335'),(CELLROOT,'Trace75BFSCellShift','b71baea359fe136c823fed0d7b462a159f5245a7eb5e2e242766edca64af5f83','757b5a9f37ede9d67c75b97714f68d2c5c2c48c48cdd8845145ccadb82e047b8'),(ALIGNROOT,'Trace75BFSAlignedShift','c98252d1ecb692a8346539c1a043228535e43fd120f0409175a157628ff83453','e031954c734ca8bbecf74a134acb9bfe2bdeeccebe2550f1a79e85dda76deb64'),(PARITYROOT,'Trace75BFSSimpleParity','01e84c924544a56a7ab69db7136cbbb3b5de5158660921b9879ee436253df9ec','c6067db34633e8bb3bd9e0efbd11c61effabd3564346f0877430b51a21944b67'),(OCCUPIEDROOT,'Trace75BFSOccupied','a82d245ff3c009d1afbb8807c10bfbd1e30167d930d34313238edf8079da47a3','ea99101894f3575e4846087cc0b798843c6ecea62ca1164bd320c2ebd7c23ad8'),(CLEANROOT,'Trace75BFSCleanCarry','83673606ed323d304cb97b95f4ad25f120dec09a286f020242d3ce226c6156e8','95408ca90bbf60fd8162eb69dc98f651aae45ca9450492b534aa978c0b0d0c2d'),(SUPPORTROOT,'Trace75BFSSupport','06187545b591ad3f6e19bd8f5f9101c6c291bed639e1e10b629584960604ee6b','0795d51ca82af5844510d53a0690ef3940d023f0c78450c38026a8386a255121'),(CARRYROOT,'Trace75BFSCarry','84b55b0b1e206c5a9e7d16292581651bbe69cbed51b4f50f8a2faf6563bf1499','d4dc1034131198fd5965e9a23585f81c1182c39ba8b217fb550036acb7b9545e'),(SLOTROOT,'Trace75FixedSlots','e33b9f4ef0132bc2fc0f1adabad939d892b22a446ec1679934f3c34d0902b7d6','63c29a06e1efa989917b77548c8362622a038fe0531373a7f86993343f80cda1')]
root=None
def stable():
 for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
 need(sha(__file__)==RUNSHA,'runner changed')
 if root is not None:check_root(root,{SRC.name,'Trace75BFSLocalWord.olean'})
 check_clients(CLIENTS)
 paths={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
 for p in lib.rglob('*'):
  if p.is_symlink():need(p.is_file(),'dangling union entry '+str(p))
 wanted={rel(n)+suffix for n,r in expected.items() for suffix,item in r.items() if item is not None};need(paths==wanted,'union inventory changed')
 for n,r in expected.items():
  cur=bundle(lib/rel(n));need(hashes(cur)==hashes(r),'union hash drift '+n)
  for s,item in r.items():
   if item is not None:need(cur[s]['resolved']==item['resolved'],'union target drift '+n+s)
 for n,r in outside.items():
  path=Path(r['.olean']['path']);search=([root] if root is not None else [])+[CASTROOT,ANCHORROOT,TILEROOT,WORDROOT,BLOCKSROOT,SPATIALROOT,DECODEROOT,FIELDROOT,RESETROOT,CELLROOT,ALIGNROOT,PARITYROOT,OCCUPIEDROOT,CLEANROOT,SUPPORTROOT,CARRYROOT,SLOTROOT,lib,PACK,CORE];need(selected(n,search)==path,'outside selection changed '+n)
  cur=bundle(Path(str(path)[:-6]));need(hashes(cur)==hashes(r),'outside bundle drift '+n)
  for s,item in r.items():
   if item is not None:need(cur[s]['resolved']==item['resolved'],'outside target drift '+n+s)
stable();pre=guard()
if args.preflight_only:
 print(json.dumps({'status':'PREFLIGHT_PASS','union':len(expected),'outside':len(outside),'subtrees':{n:len(v['project']) for n,v in subtrees.items()},'runner_sha256':RUNSHA}));raise SystemExit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
O=H/'observations'/args.attempt;need(not os.path.lexists(O),'attempt exists');O.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='trace75-bfs-localword-'));copy=root/SRC.name;shutil.copyfile(SRC,copy);shutil.copyfile(SRC,O/'source.txt');need(sha(copy)==PINS[SRC] and sha(O/'source.txt')==PINS[SRC],'source copy drift')
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(root)+':'+str(CASTROOT)+':'+str(ANCHORROOT)+':'+str(TILEROOT)+':'+str(WORDROOT)+':'+str(BLOCKSROOT)+':'+str(SPATIALROOT)+':'+str(DECODEROOT)+':'+str(FIELDROOT)+':'+str(RESETROOT)+':'+str(CELLROOT)+':'+str(ALIGNROOT)+':'+str(PARITYROOT)+':'+str(OCCUPIEDROOT)+':'+str(CLEANROOT)+':'+str(SUPPORTROOT)+':'+str(CARRYROOT)+':'+str(SLOTROOT)+':'+str(lib)+':'+str(PACK),'LEAN_NUM_THREADS':'1'};reader_env={'PATH':'/usr/bin:/bin'};output=root/'Trace75BFSLocalWord.olean'
r={'status':'FAILED','runner_sha256':RUNSHA,'inputs':{str(p):h for p,h in PINS.items()},'output_root':str(root),'provider_union':str(lib),'preflight':pre,'subtrees':subtrees,'env':env,'scope':'symbolic direct-BFS local word only; external kernel/PDF binding and historical outside/package ancestry remain open'}
def save():
 p=O/'result.tmp';p.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');os.replace(p,O/'result.json')
try:
 stable();cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(copy),'-o',str(output)];r['stage']={'status':'RUNNING','command':cmd};save()
 stage=monitored(cmd,env,O/'stdout',O/'stderr',600);r['stage'].update(stage);r['stage']['status']='CHECKING';save()
 need(stage['exit']==0 and stage['reason'] is None and output.is_file() and not output.is_symlink() and report_ok((O/'stdout').read_text(),(O/'stderr').read_text()),'Lean result or axiom report failed')
 need(sha(copy)==PINS[SRC] and sha(O/'source.txt')==PINS[SRC],'copied source changed');stable();r['object_sha256']=sha(output);r['stage']['status']='PASS';save()
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),str(output)];r['header']={'status':'RUNNING','command':cmd};save();head=monitored(cmd,reader_env,O/'header.stdout',O/'header.stderr',45);r['header'].update(head);save()
 need(head['exit']==0 and head['reason'] is None and not (O/'header.stderr').read_text(),'header failed');imports=parse_header((O/'header.stdout').read_text(),output)
 need([n for n in imports if n!='Init']==DIRECT,'unexpected serialized direct imports');need(sha(output)==r['object_sha256'] and sha(copy)==PINS[SRC] and sha(O/'source.txt')==PINS[SRC],'output/source changed');stable()
 r.update({'status':'PASS','header_imports':imports,'postflight':resources()});r['header']['status']='PASS';save();print(json.dumps({'status':'PASS','root':str(root),'object_sha256':r['object_sha256'],'result_sha256':sha(O/'result.json')}))
except BaseException as e:
 r.update({'status':'FAILED','exception':repr(e),'traceback':traceback.format_exc(),'postflight':resources()});save();raise
