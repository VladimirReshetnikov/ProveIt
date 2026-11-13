#!/usr/bin/env python3
"""Audit the adjacent-Pell descent and 80-graph join without replaying Lean."""
import ast,json,os,re,sys
from hashlib import sha256
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research';PRIOR=B/'ordinary12-direct90-ipra-join/observations/attempt03/result.json'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
ENTRIES=[
 ('ten-positive-adjacent-descent-prototype','AdjacentDenominator','attempt04','c1185203a799377e5ba757caca402c53f3eee9624ae6cc00f786afe931efecf3','83c7300a38a6d5619d9802679be749fbe8088a1be0e34c3683aecd7965dc9ff9','24099f5013a17a6c06c350527ee53d7fc9db075be2c21aa3031537933cc6ce3b'),
 ('ten-positive-adjacent-preserve-prototype','AdjacentPreserve','attempt04','b8e30924e7e6fc236477a16f6c0c70fc1522977f909f8afad88f66bca52b7ce2','bf2cef6fd83385d21a3553ca2a774273bf9b8febb0c6dedae2ef40c5e8e2e2e2','7ebeae0e91e698127a176ac79b0177508492c4b4e09d385a4145950e89e85464'),
 ('ten-positive-adjacent-bounds-prototype','AdjacentBounds','attempt06','4db573ea169893b8fb96430a48bd30a578263979f136619e8812ffa0153f4814','b6afea28cda32503292760953f1773b183089b151689af8f80d1d76a18da8101','8fc233cb7d399be1043e1b242a8a851b456271a52c6b08f6e5ac1f60f3f491f3'),
 ('ten-positive-adjacent-step-prototype','AdjacentStep','attempt04','e5c30484531c173c64a75d917d9fead0f13c0bb0b2ad74613ab64f443e4c9012','cf3fee46a9e362a5b474f1d983c25e7dc67cb65436b3c4f0625ecf1cf17710a7','b8f56fbcc020f94d8fe8619d544f69fcced24c596ea0a3e887d538130fd682cf'),
 ('ten-positive-adjacent-complete-prototype','AdjacentComplete','attempt02','aae40ace48c04ba08198efe221b8eaf06a8d1c618c103b0cec533f40fff5db2c','e75ae912b24068b600e79d93eaef81e314146b7b50e0c4268c2f6db6fd0e650b','8fe33fcc905dc8e7bd5a5300b8e73e583d93fcf03244dee89258d63f3e78e638'),
 ('ten-positive-adjacent-integer-prototype','AdjacentInteger','attempt01','1a2c56384ec3c3d9d93ca448870be05cc3f742b684ef3800e35ecbe6d024c063','19321c96c92462072fc3fe6cf30212535baa29e7915e1e59ca2c26073873dc34','51cfe265b4bbe506c785ea0f3e8f420a4f48977c05cdf3e5d9b77dc4a62b8a4b'),
 ('ten-positive-80-adjacent-prototype','Direct80Adjacent','attempt02','eeb49f9915fe29863bdaa17883bc8f78b7b991efa5e660c552c4f55714c19e72','26d181ad42cacd5f8749e0d97fcfae90660b87601574745d48fd2f815f8c98ad','ac461da9622b62696d305e4262a614f5ec98f342fae9458ffb15766098d8de2c')]
# Correct source/object pins are taken from the retained accepted receipts;
# this list fixes the expected values and the specific author observations.
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
need(sha(PRIOR)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','prior 90 receipt')
old=json.loads(PRIOR.read_text());need(old['status']=='PASS','prior join')
direct={};outputs={};samples=0;inputs={}
for directory,module,attempt,source_pin,obj_pin,terminal_pin in ENTRIES:
 root=B/directory;source=root/(module+'.lean');runner=root/'run.py';obs=root/'observations'/attempt;t=obs/'terminal.json'
 need(sha(source)==source_pin and sha(t)==terminal_pin,'source/terminal pin '+module)
 r=json.loads(t.read_text());pins=r['pins'];need(r['exit']==0 and r['reason'] is None and pins==r['after'],'author status '+module)
 need(sha(obs/'source.txt')==pins['source']==source_pin and sha(runner)==pins['runner'] and sha(LEAN)==pins['lean'],'source/runner/tool '+module)
 obj=Path(r['output_root'])/(module+'.olean');need(sha(obj)==r['object_sha256']==obj_pin,'object '+module);outputs[module]=obj_pin
 need(sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+module)
 text=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'diagnostic '+module)
 reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
 need(reports and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom reports '+module)
 pre=r['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
 for x in r['samples']:
  need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2,'resource sample');samples+=1
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean')
 need(sha(provider)==pins['direct_provider'],'direct provider pin '+module)
 tree=ast.parse(runner.read_text());assign=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='extra' for t in n.targets))
 extras=[Path(ast.literal_eval(x.args[0])) for x in assign.value.elts]
 pin_names={'AdjacentComplete':'complete','AdjacentStep':'step','AdjacentBounds':'bounds',
  'AdjacentDenominator':'denominator','AdjacentPreserve':'preserve','ProductRoot':'root',
  'TenPositiveDoubling':'doubling','ScaledSquare':'scaled'}
 expected_extra=pins['extra'] if 'extra' in pins else [pins[pin_names[x.stem]] for x in extras]
 need([sha(x) for x in extras]==expected_extra,'prototype predecessor pins '+module)
 roots=[Path(x) for x in r['lean_path'].split(':')]
 for name in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
  rel=Path(name.replace('.','/')+'.olean');selected=next((p/rel for p in roots if (p/rel).is_file()),None)
  need(selected is not None,'missing direct import '+name)
  if '.' in name:
   ns=next((p for p in roots if (p/name.split('.')[0]).is_dir()),None)
   need(ns is not None and (ns/rel).is_file(),'namespace shadow '+name)
  direct[name]={'path':str(selected),'sha256':sha(selected)}
  prior=old['post_headers']['project'].get(name)
  if prior:
   need(direct[name]['sha256']==prior['record']['sha256'],'prior 90 direct import '+name)
   stem=str(selected)[:-len('.olean')]
   for suffix,v in prior['companions'].items():
    now=rec(stem+suffix);need((None if now is None else now['sha256'])==(None if v is None else v['sha256']),'prior 90 companion '+name+suffix)
 inputs[str(source)]=source_pin;inputs[str(t)]=terminal_pin;inputs[str(obj)]=obj_pin
# Verify retained earlier attempts without treating an earlier small theorem or
# a zero exit with warnings as the accepted theorem.
history={
 'ten-positive-adjacent-descent-prototype':{'attempt01':1,'attempt02':1,'attempt03':1},
 'ten-positive-adjacent-preserve-prototype':{'attempt01':0,'attempt02':0,'attempt03':1},
 'ten-positive-adjacent-bounds-prototype':{'attempt01':1,'attempt02':1,'attempt03':0,'attempt04':0,'attempt05':1},
 'ten-positive-adjacent-step-prototype':{'attempt01':1,'attempt02':1,'attempt03':1},
 'ten-positive-adjacent-complete-prototype':{'attempt01':1},'ten-positive-80-adjacent-prototype':{'attempt01':1}}
history_pins={
 'ten-positive-adjacent-descent-prototype':['0aa881b1210bc6f3aeef3b66162d9c36ce465384db6a9181594d29725878982f','745ed46b204af31a54d613e7feed4ebcfbb30a2c6fa86e0cb71429a88cef7e76','e063e96378f10d3e03cf2c77e65bf07a9bc66f5d5d65974ac2242ff176308220'],
 'ten-positive-adjacent-preserve-prototype':['c02dab940b96806297b42730d9b1f908f74e6288a92abb8aee0e3ca0a4d315c7','88236f2b73c43160e95f1441eea8138301bac86c60a7daa7e814b2b24a2b88d4','7215ee7522786a67765a3d21507c800e298f08a31074b5c561563404da2da1a2'],
 'ten-positive-adjacent-bounds-prototype':['f0072288feda12adca360169325d82df28f85b98cb8244aa55ebb5e8fcdc9895','f8760f883ae06f4d17100809d2604d4b71077ee5931484fa1fa3710f6d2294c4','c300f0388f7ff73201b05d0cd8ed4ba8c141d4c06044b24b3c4d489a5a99c216','79ac61f98d35efe987c023bcf7b0d81b9d86aea28192f0ff0b51e3b86f2ab941','6de6e42aff0a5065c8a2cd2f3fc231063f17d3a7a6ddb486409071f0d696b2d8'],
 'ten-positive-adjacent-step-prototype':['113cdc4e5e118d1325268639b79c555d5965959b0df0364db878a187fd17cb80','90f439f4228a72a43f4e98a9a1c26783e4b416cebb300269b2e787f348f3e5a7','147500ee4648257f38c9461751132fcb5731a82636e0d28db87aed4ff41164e7'],
 'ten-positive-adjacent-complete-prototype':['1eb8a131b0bc915bdbb1503241eed457acd4c2b387d2ba9c341e8243116a5653'],
 'ten-positive-80-adjacent-prototype':['773c1bfd3b9279b1726d826c5cd36cd4faa0c25e0b2f20d06aa2d664100093b9']}
for directory,cases in history.items():
 for name,code in cases.items():
  obs=B/directory/'observations'/name;digest=history_pins[directory][int(name[-2:])-1]
  need(sha(obs/'terminal.json')==digest,'historical receipt pin '+directory+'/'+name)
  inputs[str(obs/'terminal.json')]=digest
  r=json.loads((obs/'terminal.json').read_text());log=(obs/'stdout').read_text()+(obs/'stderr').read_text()
  need(r['exit']==code and sha(obs/'source.txt')==r['pins']['source'] and sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'],'prior attempt '+directory+'/'+name)
  if code:need('error' in log,'missing failure diagnostic '+name)
need('warning:' in (B/'ten-positive-adjacent-bounds-prototype/observations/attempt03/stdout').read_text(),'warning-rejected attempt')
den=(B/ENTRIES[0][0]/'AdjacentDenominator.lean').read_text();step=(B/ENTRIES[3][0]/'AdjacentStep.lean').read_text();complete=(B/ENTRIES[4][0]/'AdjacentComplete.lean').read_text();integer=(B/ENTRIES[5][0]/'AdjacentInteger.lean').read_text();graph=(B/ENTRIES[6][0]/'Direct80Adjacent.lean').read_text()
need('denominator_square_divides' in den and 'Bez r m 1' in den,'denominator assumptions')
need('∃ v\' r\' : V, 0<v\' ∧ v\'<v ∧ Bez r\' m 1' in step,'strict step')
need('𝚺₁-Predicate P' in complete and 'InductionOnHierarchy.least_number' in complete and 'adjacent_step B m w s' in complete and ': m=1' in complete,'internal least-number descent')
need('gcd_certificate_exists z M' in integer and 'denominator_one B m v r' in integer and '∃ y : V, z=M*y' in integer,'integral quotient')
need('(hb : 0<(p 0:V)) (hv : ∀j,0<v j)' in graph and 'InternalZero (graph (integerPorts p)).output v' in graph and 'quotient_of_scaled_norm B S V0 Z0' in graph and 'Q*(V0*V0)=1+(Q-1)*(y*y)' in graph,'graph join scope')
for path,digest in inputs.items():need(sha(path)==digest,'input changed '+path)
for name,row in direct.items():need(sha(row['path'])==row['sha256'],'direct import changed '+name)
print(json.dumps({'status':'PASS','accepted_modules':outputs,'direct_imports':direct,'earlier_attempts':sum(map(len,history.values())),
 'resource_samples':samples,'scope':'source/receipt and point-in-time direct provider audit; no Lean replay, full package/dynamic/source-object ancestry, halt or iPRA theorem'},indent=2,sort_keys=True))
