#!/usr/bin/env python3
"""Plan a source-pinned trace75 replay against the coherent BFS project union."""
from pathlib import Path
from hashlib import sha256
import json,os,sys,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];T=D/'research/trace75-root-probe';ROOT=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib')
SCAN=D/'research/trace75-bfs-provider-preflight/observations/scan-attempt01/result.json';OUTER=D/'research/trace75-bfs-provider-preflight/observations/outer-attempt01/terminal.json';BFS=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json'
PINS={SCAN:'e27f1cb8694aab43a1023abcce95f7fbc7846d4860dac4b96046391da3dd1e8d',OUTER:'5a916a82f6bf12f2102f00d48183229c669aeda6fc760edeb4df670c17b468c7',BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559'}
ATT={'Trace75ProductHeight':'productheight-attempt01','Trace75GraphPower':'graphpower-attempt03','Trace75GraphUnweighted':'unweighted-attempt01','Trace75RadixAlignment':'radixalignment-attempt02','Trace75SandwichBoth':'sandwichboth-attempt02','Trace75Kappa':'kappa-attempt02','Trace75Repunit':'repunit-attempt01','Trace75IntegralTransport':'integraltransport-attempt01','Trace75Population':'population-attempt01','Trace75NaturalTransport':'naturaltransport-attempt01','Trace75Saturation':'saturation-attempt01','Trace75FixedSaturation':'fixedsaturation-attempt02','Trace75FixedDigits':'fixeddigits-attempt01','Trace75FixedCongruence':'fixedcongruence-attempt01'}
O=H/'observations/plan-attempt01';SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash']
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),'not file '+str(p));return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(p):return {s:rec(Path(str(p)+s)) for s in SUFFIXES}
need(not O.exists(),'observation exists');runner=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'receipt drift '+str(p))
x=json.loads(SCAN.read_text());outer=json.loads(OUTER.read_text());bfs=json.loads(BFS.read_text());need(x['status']=='PASS' and outer['exit']==0 and bfs['status']=='PASS','input status')
headers=x['headers'];names=set(x['roots']['Trace75FixedCongruence']['project']); seeds={'DiophantineConsistency.ModelRatioBounds','DiophantineConsistency.ArithmeticNegativeNorms'};need(seeds<=names,'seed ancestry')
affected=set(seeds)
while True:
 new=affected|{n for n in names if set(headers[n])&affected}
 if new==affected:break
 affected=new
stages={n for n in affected if n.startswith('Trace75')};need(stages==set(ATT),'affected stage set changed')
remaining=set(stages);order=[]
while remaining:
 layer=sorted(n for n in remaining if not(set(headers[n])&remaining));need(layer,'cycle in stages');order+=layer;remaining-=set(layer)
classification={'identical':{},'different':{},'absent':{}}
for n in sorted(names):
 sel=x['selected_project'][n];stem=ROOT/Path(*n.split('.'));fresh=bundle(stem)
 if fresh['.olean'] is None:kind='absent'
 elif fresh['.olean']['sha256']!=sel['.olean']['sha256']:kind='different'
 else:
  need(all((None if sel[s] is None else sel[s]['sha256'])==(None if fresh[s] is None else fresh[s]['sha256']) for s in SUFFIXES),'same object but companion difference '+n)
  kind='identical'
 classification[kind][n]={'trace':sel,'fresh':fresh}
need([len(classification[k]) for k in ('identical','different','absent')]==[152,10,46],'unexpected classification')
producers={}
for n in order:
 src=T/(n+'.lean');att=T/'observations'/ATT[n];receipt=att/'terminal.json';r=json.loads(receipt.read_text())
 need(r['exit']==0 and r['reason'] is None and r['object_sha256']==x['selected_project'][n]['.olean']['sha256'],'producer status/object '+n)
 need(sha(src)==r['inputs'][str(src)]==sha(att/'source.txt'),'source mismatch '+n)
 need(sha(att/'stdout')==r['stdout_sha256'] and sha(att/'stderr')==r['stderr_sha256'],'log mismatch '+n)
 producers[n]={'source':str(src),'source_sha256':sha(src),'receipt':str(receipt),'receipt_sha256':sha(receipt),'object_sha256':r['object_sha256'],'stage_imports':[m for m in headers[n] if m in stages]}
for n in x['roots']['DirectBFSBandCarry']['project']:
 need(n not in classification['different'] and n not in classification['absent'],'BFS subtree incompatible '+n)
for n in names:
 snap=x['selected_project'][n];need(bundle(Path(snap['.olean']['path'][:-6]))==snap,'trace selected drift '+n)
for n in names:
 fresh=classification[next(k for k in classification if n in classification[k])][n]['fresh'];need(bundle(ROOT/Path(*n.split('.')))==fresh,'fresh selected drift '+n)
for p,h in PINS.items():need(sha(p)==h,'receipt drift after')
need(sha(__file__)==runner,'runner drift');O.mkdir(parents=True)
r={'status':'PASS','inputs':{str(p):h for p,h in PINS.items()},'runner_sha256':runner,'root':'Trace75FixedCongruence','seeds':sorted(seeds),'affected':sorted(affected),'stage_order':order,'producers':producers,'classification':classification,'scope':'read-only planning from observed header graph and current object/companion/source hashes; no replay, no package or historical provenance guarantee'}
(O/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','stages':len(order),'classification':{k:len(v) for k,v in classification.items()},'sha256':sha(O/'result.json')}))
