#!/usr/bin/env python3
"""Independent graph, source and captured receipt audit; no Lean replay."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(x,s):
    if not x:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];d=base/'research'/'p64-qcube72-free-main-candidate';parent=base/'research'/'p64-qcube76-independent-y-candidate'/'graph.json'
need(sha(parent)=='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c','parent pin')
a=json.loads(parent.read_text()); b=json.loads((d/'graph.json').read_text())
removed={'r_plus_one','r','U_gamma','main_gap'}
need([r for r in a['source'] if r[0] in removed]==[['r_plus_one','-','k','R'],['r','-','r_plus_one',1],['U_gamma','*','U','gamma'],['main_gap','-','U_gamma','r']],'removed gates')
expect=[['H_main_gap','*','H','h'] if r[0]=='H_main_gap' else r for r in a['source'] if r[0] not in removed]
need(b['source']==expect and len(expect)==72 and b['witnesses']==a['witnesses'][:-1]+['h'] and b['fixed_numerals']==a['fixed_numerals'],'graph transform')
need({op:sum(r[1]==op for r in expect) for op in ('*','+','-')}=={'*':41,'+':18,'-':13},'operation counts')
source=(d/'P64QCube72Free.lean').read_text();block=source.split('-- BEGIN GENERATED GRAPH\n')[1].split('  -- END GENERATED GRAPH')[0]
def parse(s):return int(s) if s.isdecimal() else s
leanrows=[]
for line in block.splitlines():
    m=re.fullmatch(r'  let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)',line);need(m is not None,'Lean row parse')
    name,x,op,y=m.groups();leanrows.append([name,op,parse(x),parse(y)])
need(leanrows==expect,'Lean transcription rows')
for i,n in enumerate(b['witnesses']):need(f'let {n} : Expr (Fin 14) := .var {i}' in source,'witness index')
for i,n in enumerate(b['fixed_numerals']):need(f'let {n} : Expr (Fin 14) := .constant (p {i})' in source,'port index')
need('⟨A0, M, W, Na, Lt, polynomial⟩' in source,'output tuple')
# Independently check live rows and selected theorem scope.
live=set();todo=['polynomial'];table={r[0]:r[2:] for r in expect}
while todo:
    n=todo.pop()
    if n in live or n not in table:continue
    live.add(n);todo.extend(x for x in table[n] if isinstance(x,str))
need(live==set(table),'dead graph gate')
binding=(d/'P64QCube72FreeBinding.lean').read_text();forward=(d/'P64QCube72FreeForward.lean').read_text()
for tok in ('[CommRing R]','Function.update v 13 (gap p v)','theorem output','P64QCube76Y.graph p).output.evalRing v'):
    need(tok in binding,'binding source '+tok)
for tok in ('[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','theorem exists_zero','(hv : ∀ i, 0 < v i)',
            'P64QCube76Y.graph','P64QCube72Free.graph','exists_positive_main_gap','Function.update v 13 h',
            'P64QCube72FreeBinding.output'):
    need(tok in forward,'forward source '+tok)
need(all(not re.search(r'\b(?:sorry|admit|axiom)\b',s) for s in (source,binding,forward)),'source admission')
stages={'graph':('P64QCube72Free.lean','check_graph_lean.py',''),
 'binding':('P64QCube72FreeBinding.lean','check_binding_lean.py',"'P64QCube72FreeBinding.output' depends on axioms: [propext]\n"),
 'forward':('P64QCube72FreeForward.lean','check_forward_lean.py',"'P64QCube72FreeForward.exists_zero' depends on axioms: [propext, Classical.choice, Quot.sound]\n")}
receipts={};objects={}
for stage,(src,runner,expected_log) in stages.items():
    path=d/'observations'/stage/'result.json';r=json.loads(path.read_text())
    need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and
         r['guards_before']==r['guards_after'] and r['group_rss_samples']>0,'receipt '+stage)
    for p,info in r['guards_after'].items():
        p=Path(p)
        if info is None:need(not os.path.lexists(p),'shadow present '+str(p))
        else:need(p.is_file() and str(p.resolve())==info['realpath'] and sha(p)==info['sha256'],'guard drift '+str(p))
    need(sha(d/runner)==r['runner_sha256'] and sha(d/'missing_child.py')==r['missing_child_helper_sha256'],'runner/helper '+stage)
    need(str(d/src) in r['guards_after'] and sha(d/src)==r['guards_after'][str(d/src)]['sha256'],'source guard '+stage)
    cmd=r['command'];obj=Path(cmd[-1]);log=obj.parent/'compile.log'
    need(obj.is_file() and not obj.is_symlink() and sha(obj)==r['object_sha256'],'object '+stage)
    need(log.is_file() and sha(log)==r['log_sha256'] and log.read_text()==expected_log,'complete log '+stage)
    need((obj.parent/'result.json').read_bytes()==path.read_bytes(),'copied receipt '+stage)
    receipts[stage]=sha(path);objects[stage]=r['object_sha256']
# Direct stage-to-stage provider links, including already reviewed positivity.
rbind=json.loads((d/'observations'/'binding'/'result.json').read_text());rfwd=json.loads((d/'observations'/'forward'/'result.json').read_text())
def expected_in_guard(r,h):return any(isinstance(x,dict) and x.get('sha256')==h for x in r['guards_after'].values())
need(expected_in_guard(rbind,objects['graph']),'graph to binding link')
yreceipt=base/'research'/'p64-qcube76-independent-y-guarded-check'/'observations'/'attempt04'/'result.json'
y=json.loads(yreceipt.read_text())
need(y['status']=='PASS' and y['exit']==0 and expected_in_guard(rbind,y['object_sha256']), '76Y to binding link')
need(expected_in_guard(rfwd,objects['binding']),'binding to forward link')
pos=json.loads((base/'research'/'p64-qcube72-forward-graph-draft'/'observations'/'attempt03'/'result.json').read_text())
need(pos['status']=='PASS' and expected_in_guard(rfwd,pos['object_sha256']),'positivity to forward link')
out={'status':'PASS_GRAPH_SCOPE_AND_RECEIPT_REVIEW','script_sha256':sha(__file__),
     'parent_sha256':sha(parent),'graph_sha256':sha(d/'graph.json'),'lean_graph_sha256':sha(d/'P64QCube72Free.lean'),
     'receipt_sha256':receipts,'object_sha256':objects,'positivity_object_sha256':pos['object_sha256'],
     'old_76y_receipt_sha256':sha(yreceipt),'old_76y_object_sha256':y['object_sha256'],
     'operations':72,'counts':{'*':41,'+':18,'-':13},
     'scope':'Read-only structural and direct-receipt review, no Lean replay or transitive ancestry; only the forward map is proved.'}
print(json.dumps(out,indent=2,sort_keys=True))
