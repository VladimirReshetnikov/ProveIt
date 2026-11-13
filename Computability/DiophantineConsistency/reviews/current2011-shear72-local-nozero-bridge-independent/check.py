#!/usr/bin/env python3
"""Independent comparison of local bridge and the selected lexical DAG."""
import copy,hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear72-local-nozero-bridge-selection/README.md':'4e1b9502bcbb4331eb21beb1c623493d380b6a5a4d139b53bc7a5258115a7e1f',
'research/current2011-shear72-local-nozero-bridge-selection/Shear72ConditionalIPRA.lean.src':'fb047ee1f04e1e9a4b1625a6c4e7f37776e8fb4b8146e6263238dc925309415e',
'research/current2011-shear72-local-nozero-bridge-selection/Shear72JointIPRA.lean.src':'ec200112adb96b65953706576893466dc03dfe001dd4873489c8d56e60b92bae',
'research/current2011-shear72-local-nozero-bridge-selection/check.py':'cb76e3e6f1429a235424a7759441979b9b45d477304bba974ad068eafd895df0',
'research/current2011-shear72-local-nozero-bridge-selection/pins.json':'8aff5bd258b81fdd564e9d62ddd93810a01319fe25ef35290c3bd6737fe6d3a1',
'research/current2011-shear72-local-nozero-bridge-selection/selection.json':'3ff32c2bc77e08ca2b784c382bc74e169c7b77161311141267e41705c6fecc65',
'research/current2011-shear72-local-nozero-bridge-selection/receipt.json':'c4f1a975825337f6f9ad075bd824f01a735bef99411a5d61904bfba72bc4d928',
'research/current2011-shear72-order-carrier-selection/selection.json':'99f0c58805d16583f44598c8cee4282d1f5a57c1798630b9bb8bdc798a2c99b7',
'research/current2011-shear72-joint-ipra-source-plan/Shear72JointIPRA.lean.src':'ba0c3a10a368062753e3b99b183614a8bf59ef90c0bd94749e3d0ff0bc19428a',
'research/current2011-shear72-conditional-ipra-endpoint-draft/Shear72ConditionalIPRA.lean.src':'4345be11f816398c435b92cf647ea2345014bc84d3868b82512cb0a43e953287',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/HAExpressionAssembly.lean':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e',
'Lean/DiophantineConsistency/FoundationHANoZero.lean':'8539882d474478c041177ed90eae788ff02167a7c15621117287e4ab3904eb60',
'research/current2011-ordinary71-60-ipra/OrdinarySphere7160IPRA.lean':'a169a2e71e6699ef84f6196f43ef3bb54245208213cc32f776adadfa622f4421'}
def need(b,m):
 if not b:raise RuntimeError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return (root/p).read_text()
for p,h in pins.items():need(sha((root/p).read_bytes())==h,'pin '+p)
d='research/current2011-shear72-local-nozero-bridge-selection/';old=read('research/current2011-shear72-conditional-ipra-endpoint-draft/Shear72ConditionalIPRA.lean.src');new=read(d+'Shear72ConditionalIPRA.lean.src');up=read('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean')
def block(text,left,right):return text.split(left,1)[1].split(right,1)[0]
need(block(new,'def SameNoZero ','\n\n')==block(up,'def SameNoZero ','\n\n'),'local exact SameNoZero')
need(block(new,'def ParentToChild : Prop :=','/-- The bridge')==block(old,'def ParentToChild : Prop :=','/-- The bridge'),'map propositions and proof unchanged')
need(new.split('theorem native_equivalence72',1)[1]==old.split('theorem native_equivalence72',1)[1],'endpoint tail unchanged')
for v in ['rw [classicalNoZero_iff, classicalNoZero_iff]','simpa only [InternalZero, ne_eq] using same_no_zero forward reverse V','exact eqv.trans (OrdinarySphere7160IPRA.bridge71 V)']:
 need(v in new,'local bridge '+v)
for v in ['rw [classicalNoZero_iff, classicalNoZero_iff]','simpa only [InternalZero, ne_eq] using h V','exact eqv.trans (hf V)']:
 need(v in up,'generic bridge '+v)
assembly=read('Lean/DiophantineConsistency/HAExpressionAssembly.lean');foundation=read('Lean/DiophantineConsistency/FoundationHANoZero.lean')
need('theorem classicalNoZero_iff' in assembly and 'def PolynomialBridge' in assembly and 'def classicalNoZero' in foundation,'semantic interfaces')
joint0=read('research/current2011-shear72-joint-ipra-source-plan/Shear72JointIPRA.lean.src');joint1=read(d+'Shear72JointIPRA.lean.src');before='open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv\n';after='open AdaptiveEquationSyntax2011 HAExpressionAssembly\n'
need(joint0.count(before)==1 and joint0.replace(before,after,1)==joint1,'joint one-line delta')
need('open Shear72ConditionalIPRADraft' in joint1 and 'same_no_zero parent_to_child child_to_parent' in joint1,'local resolution/use')
prev=json.loads(read('research/current2011-shear72-order-carrier-selection/selection.json'));sel=json.loads(read(d+'selection.json'));expected=copy.deepcopy(prev)
for k in ('DiophantineConsistency.Shear72ConditionalIPRA','DiophantineConsistency.Shear72JointIPRA'):expected['drafts'][k]=sel['drafts'][k]
expected['frontier'].pop('DiophantineConsistency.HAExpressionNoZeroEquiv');need(expected==sel,'exact selection delta')
headers={};used=set()
for n,v in sel['drafts'].items():
 data=(root/v['path']).read_bytes();imports=[x.split()[1] for x in data.decode().splitlines() if x.startswith('import ')]
 need(sha(data)==v['sha256'] and imports==v['imports'],'selected '+n);headers[n]=imports
 for dep in imports:
  if dep not in sel['drafts']:need(dep in sel['frontier'],'unknown '+dep);used.add(dep)
need(used==set(sel['frontier']),'frontier exact')
for n,v in sel['frontier'].items():
 if v['kind']!='external-unexamined':need(sha((root/v['path']).read_bytes())==v['sha256'],'frontier '+n)
todo=['DiophantineConsistency.Shear72JointIPRA'];seen=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(x for x in headers[n] if x in headers)
need(seen==set(headers),'reachability')
remaining=set(headers)
while remaining:
 ready={n for n in remaining if all(x not in remaining for x in headers[n] if x in headers)}
 need(ready,'cycle');remaining-=ready
# Both map assumptions imply equality of no-zero propositions in each model.
for parent in (False,True):
 for child in (False,True):
  forward=(not parent) or child;reverse=(not child) or parent
  if forward and reverse:need((not child)==(not parent),'contrapositive direction')
print(json.dumps({'source_pins_verified':len(pins),'identical_local_SameNoZero':True,'map_definitions_and_proof_unchanged':True,'endpoint_tail_unchanged':True,'joint_open_delta_exact':True,'selected_drafts':len(headers),'direct_frontier':len(sel['frontier']),'removed_direct_frontier':'DiophantineConsistency.HAExpressionNoZeroEquiv','scope':'lexical comparison only; no Lean elaboration, transitive provider or endpoint verification'},sort_keys=True,indent=2))
