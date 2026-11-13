#!/usr/bin/env python3
"""Independently compare row syntax and audit paired model-binding artifacts."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen69-dag-binding'
GRAPH=BASE/'research/thirteen-variable-independent/polynomial69.json'
OUT=Path('/tmp/ipra-thirteen69-dag-pair-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='7308f91874506cc8e5bce17db9f13387d42d1c0f5c2acc70893b459ffb46ff33'
NAMES=('ShortEquation','ThirteenCarrier','Thirteen69Nodes','Thirteen69Cuts')
SRCS=('2d447a166a33dedb90c8acdf0755d584a9d057bf46a047e0a454bf150f628b68','2f19e9690841d15d48a281cfafd8813270e0dcfe38a9f6c68ab9d2f9d85453ca','599ec909c6605024c41ad45287d8b944e488fbe82e1d1e0d559b4a5b4d38d02e','3e3258bda47ca0843eed32fdbfd69f9d1dc57b7def815d2d59a2fdbd07093d66')
OBJS=('6aaa12eec5f197a5fe816c33982c3fb48de96ecdf76f4374ea4da34197885ffd','54da7156e0795e6c91b225c12bd2f0965a3cad69752e6f0fa8eeb52337c2733e','e365a6efd41d2584d1ab95fb86b348ba16060b462debc78498b4e2702199525c','d997c252087f2d34576afae7966f810e38fca154765f9352b404f5928e930680')
WIT=('J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma')
PORT=('beta','K0','MC','MF')

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [*(PKG/x for x in ('README.md','replay.py','check_rows.py','Thirteen69Nodes.lean','Thirteen69Cuts.lean','replay-receipt.json','terminal-observation.json')),
              *(BASE/'Lean/DiophantineConsistency'/(x+'.lean') for x in NAMES[:2]),GRAPH]:
        blob=subprocess.run(['git','show','047484be73:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    need(sha(GRAPH)=='3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f','graph pin')
    graph=json.loads(GRAPH.read_bytes());rows=graph['source'];text=(PKG/'Thirteen69Nodes.lean').read_text()
    block=text.split('section Generic\n',1)[1].split('end Generic\n',1)[0]
    matches=re.findall(r'^def node_(\w+) \(p : Fin 4 → R\) \(v : Fin 13 → R\) : R := (.+) ([+*\-]) (.+)$',block,re.M)
    need(len(matches)==len(rows)==69 and graph['output']=='polynomial' and tuple(graph['witnesses'])==WIT and tuple(graph['fixed_numerals'])==PORT,'row structure')
    def decode(s):
        if re.fullmatch(r'\d+',s):return int(s)
        v=re.fullmatch(r'\(v (\d+)\)',s)
        if v:return WIT[int(v.group(1))]
        p=re.fullmatch(r'\(p (\d+)\)',s)
        if p:return PORT[int(p.group(1))]
        n=re.fullmatch(r'\(node_(\w+) p v\)',s)
        if n:return n.group(1)
        raise ValueError('operand '+s)
    derived=[[name,op,decode(left),decode(right)] for name,left,op,right in matches]
    need(derived==rows,'independent row-by-row comparison')
    allnames={name for name,_,_,_ in rows};need(len(allnames)==69,'node uniqueness')
    available=set(WIT)|set(PORT);counts=Counter();used=set()
    for name,op,left,right in rows:
        for arg in (left,right):
            if isinstance(arg,str):need(arg in available,'not topological '+arg);used.add(arg)
            else:need(arg in (1,3,4),'literal')
        counts[op]+=1;available.add(name)
    need(dict(counts)=={'*':39,'+':16,'-':14} and set(WIT+PORT)<=used,'count and port/variable coverage')
    live={'polynomial'}
    for name,op,left,right in reversed(rows):
        if name in live:live.update(x for x in (left,right) if isinstance(x,str) and x in allnames)
    need(allnames==live,'graph liveness')
    need('node_polynomial (fun j => .constant (p j)) .var' in text,'literal output')
    cuts=(PKG/'Thirteen69Cuts.lean').read_text()
    need('positiveShift (literal CurrentWindowCarry2011.ports)' in cuts,'fixed shifted literal')
    masks=(BASE/'Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text()
    kernel=(BASE/'Lean/DiophantineConsistency/CurrentKernelData2011.lean').read_text()
    need('def radix : ℕ := 2 ^ 47' in masks and 'def beta : ℕ := radix ^ 2011 - 1' in masks and
         '![beta, K, lowPort, highPort + beta]' in masks and
         'def K : ℕ := rawWord radix' in kernel and 'CurrentMasks2011.ports (K : ℤ)' in kernel,'exact 2011 port definitions')
    phasefile=BASE/'candidates/one-page-phase-split-carrier65-2471/coefficients/beta.bin.gz'
    phase=int.from_bytes(gzip.decompress(phasefile.read_bytes()),'big')
    need(phase==(1<<(47*2471))-1 and phase!=(1<<(47*2011))-1,'distinct beta')
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==17498 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN69_DAG '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN69_DAG' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    comparator=BASE/'research/fresh-project-closure/compare.py'
    p=subprocess.run([sys.executable,'-I','-S',str(comparator),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')],capture_output=True,timeout=120)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==r['parent_comparison'],'parent comparator')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PAIR/side/'child-output/lib/DiophantineConsistency'
        links=row['parent_links_sha256'];need(row['label']==side and len(links)==64 and set(links)=={str(proj/p.name) for p in prior.glob('*.olean')},'parent coverage')
        for link,h in links.items():
            q=Path(link);need(q.is_symlink() and q.resolve()==(prior/q.name).resolve() and sha(q)==h,'link '+link)
        bb=run/'lib/BusyBeaver';need(bb.is_symlink() and bb.resolve()==(PAIR/side/'child-output/lib/BusyBeaver').resolve(),'BusyBeaver')
        need(len(row['modules'])==4,'module count')
        for i,(item,name) in enumerate(zip(row['modules'],NAMES)):
            src=run/'src/DiophantineConsistency'/(name+'.lean');obj=proj/(name+'.olean')
            need(item['name']==name and item['exit']==item['deps_exit']==0 and not item['stderr'],'child exits')
            need(sha(src)==item['source_sha256']==SRCS[i] and not obj.is_symlink() and sha(obj)==item['object_sha256']==OBJS[i],'source/object '+name)
            need(item['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and item['command'][-1]==str(obj),'command')
            imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);deps={str(PACKAGE/'Init.olean')}
            for dep in imports:
                target=(run/'lib' if dep.startswith(('DiophantineConsistency.','BusyBeaver.')) else PACKAGE)/Path(*dep.split('.')).with_suffix('.olean')
                need(target.is_file(),'dependency '+dep);deps.add(str(target))
            need(set(item['deps_stdout'].splitlines())==deps,'direct deps '+name)
            need(not re.search(r'warning:|error:|sorryAx|\bsorry\b',item['stdout']),'warnings or admissions')
            reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",item['stdout'],re.M)
            expected=[[],[],[('Thirteen69Nodes.eval_literal','propext')],
              [('Thirteen69Cuts.scalar_eq','propext, Quot.sound'),('Thirteen69Cuts.literal_value','propext, Quot.sound')]+[(f'Thirteen69Cuts.{n}','propext, Classical.choice, Quot.sound') for n in ('internal_zero','shifted_zero','current_zero')]][i]
            need(reports==expected and item['axiom_reports']==[a for _,a in expected],'axiom reports')
        summaries.append({'side':side,'parent_links':64,'recorded_compiler_exits':[0]*4,'recorded_dependency_exits':[0]*4,'object_hashes':list(OBJS)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN69_DAG_AUDIT','source_commit':'047484be73',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':17498,'recorded_outer_exit':0,
      'independently_parsed_rows':69,'live_rows':len(live),'operation_counts':dict(counts),'variables':list(WIT),'ports':list(PORT),
      '2011_beta_exponent':47*2011,'phase2471_beta_exponent':47*2471,'parent_comparator_rerun_exit':0,'runs':summaries,
      'scope':'External exact row comparison and read-only paired suffix audit; no Lean JSON parser, 2011 degree, all-model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
