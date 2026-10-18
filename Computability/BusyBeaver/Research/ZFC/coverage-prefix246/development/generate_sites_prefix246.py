#!/usr/bin/env python3
"""Generate bounded actual-tree prefix246 coverage units; never invoke Lean.

The literal parser chooses a frontier only. Every leaf block is a closed Lean
kernel decision about descend ActualTree254.tree, and each composition theorem
requires BOTH actual child subtrees. The generated final theorem is unavailable
until all selected modules and their imports have been checked.
"""
from __future__ import annotations
import argparse, hashlib, json, re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

TREE_SHA='7f4a3782f4ce061478a233d15272c15f2b2aedab688f728f7e7511f186216e71'
BASE_IMPORTS=['ActualTree254','SiteCoverage','SitePrefix246']
NS='SetTheory.BusyBeaver.ZFC.SitesPrefix246'

@dataclass
class Tree:
    edge: tuple[str,int]|None=None
    left: Tree|None=None
    right: Tree|None=None
    @property
    def counts(self):
        if self.edge is not None:
            return (0,1,2 if self.edge[0]=='decnz' else 1,0)
        a,b=self.left.counts,self.right.counts
        return (1+a[0]+b[0],a[1]+b[1],a[2]+b[2],1+max(a[3],b[3]))

def literal_tree(path):
    raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==TREE_SHA
    text=raw.decode();body=text.split('def tree : Tree :=',1)[1].split('theorem tree_eq',1)[0]
    token=re.compile(r'\s*(\.[A-Za-z]+|[()]|[0-9]+)')
    tokens=[];at=0
    while body[at:].strip():
        m=token.match(body,at);assert m,(at,body[at:at+60])
        tokens.append(m[1]);at=m.end()
    pos=0
    def take():
        nonlocal pos
        t=tokens[pos];pos+=1;return t
    def edge():
        k=take()
        if k=='(':
            e=edge();assert take()==')';return e
        assert k in ['.inc','.decnz','.brk','.cont','.halt']
        return (k[1:],0 if k=='.halt' else int(take()))
    def tree():
        t=take()
        if t=='(':
            r=tree();assert take()==')';return r
        if t=='.node':return Tree(left=tree(),right=tree())
        assert t=='.leaf',t
        return Tree(edge=edge())
    result=tree();assert pos==len(tokens)
    assert result.counts==(6459,6460,8391,34)
    return result

def bits(xs):return '['+', '.join('true' if x else 'false' for x in xs)+']'
def goal(path):return ('allSites SitePrefix246.checkSite '+bits(path[::-1])+'\n'
                       '      (descend ActualTree254.tree '+bits(path)+') = true')
def header(imports):
    return ''.join('import BusyBeaver.ZFC.'+m+'\n' for m in dict.fromkeys(BASE_IMPORTS+imports))+'''\n/-!
Generated closed actual-tree coverage for the exact246 table and checker.
Every cut is a kernel decision about the imported actual decoder subtree.
Every structural join requires both actual children. No external coverage
premise, native evaluation or enlarged proof limits. Grouping changes only
file boundaries, never the cut propositions or the full coverage statement.
Adapted from the maintained permutation252 and prefix250 generators, preserving
Mira-Cult, Jeff Ketchersid and Wade's program and simulation attribution.
-/
namespace '''+NS+'\nopen RegisterPath RMBisim SiteCoverage\n\n'
def footer():return '\nend '+NS+'\n'
def audit(module,probes,goals):
    s='import BusyBeaver.ZFC.'+module+'\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesPrefix246\n\n'
    for p in probes:s+='#print axioms '+NS+'.'+p+'\n'
    for p,g in zip(probes,goals):s+='\nexample : '+g+' := '+p+'\n'
    return s

def build_plan(repo,cap=64,joins_per_module=16,cuts_per_module=1,max_batch_guards=64,representatives=False):
    tree=literal_tree(repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ActualTree254.lean')
    cuts=[];joins=[]
    def split(t,path):
        if t.counts[2]<=cap:
            i=len(cuts);cuts.append(dict(index=i,path=path,nodes=t.counts[0],leaves=t.counts[1],guards=t.counts[2],depth=t.counts[3],theorem=f'block_{i}'))
            return ('cut',i)
        assert t.edge is None
        left,right=split(t.left,path+[False]),split(t.right,path+[True])
        i=len(joins);joins.append(dict(index=i,path=path,theorem=f'join_{i}',left=left,right=right,module=f'SitesPrefix246Join{i//joins_per_module:03d}'))
        return ('join',i)
    root=split(tree,[])
    assert sum(c['leaves']for c in cuts)==6460 and sum(c['guards']for c in cuts)==8391
    assert len(joins)==len(cuts)-1
    isolated={0,42,210} if cap==64 else {0}
    if representatives:assert cap==64 and len(cuts)==233
    batches=[];current=[];guard_sum=0
    def flush():
        nonlocal current,guard_sum
        if current:batches.append(current);current=[];guard_sum=0
    for c in cuts:
        if c['index'] in isolated:
            flush();batches.append([c]);continue
        if current and (len(current)>=cuts_per_module or guard_sum+c['guards']>max_batch_guards):flush()
        current.append(c);guard_sum+=c['guards']
    flush()
    for i,cs in enumerate(batches):
        module=f"SitesPrefix246Chunk{cs[0]['index']:03d}" if len(cs)==1 else f'SitesPrefix246Batch{i:03d}'
        for c in cs:c['module']=module
    files={};units=[]
    def unit(module,source,probes,goals,meta,aud=None):
        au=audit(module,probes,goals) if aud is None else aud
        files[module+'.lean']=source.encode();files[module+'.audit.lean']=au.encode()
        units.append(dict(module='BusyBeaver.ZFC.'+module,source=module+'.lean',source_sha256=hashlib.sha256(source.encode()).hexdigest(),audit=module+'.audit.lean',audit_sha256=hashlib.sha256(au.encode()).hexdigest(),probe_names=probes,probes=len(probes),callers=len(goals),imports=re.findall(r'^import (\S+)',source,re.M),**meta))
    for cs in batches:
        if representatives and cs[0]['index'] not in isolated:continue
        text=header([])
        for c in cs:text+=f"/-- Cut {c['index']}: {c['leaves']} leaves, {c['guards']} guards. -/\ntheorem {c['theorem']} :\n    {goal(c['path'])} := by decide +kernel\n\n"
        unit(cs[0]['module'],text+footer(),[c['theorem']for c in cs],[goal(c['path'])for c in cs],dict(kind='closed_cuts',cuts=[c['index']for c in cs],guards=sum(c['guards']for c in cs),leaves=sum(c['leaves']for c in cs)))
    def endpoint(ref):return (cuts if ref[0]=='cut' else joins)[ref[1]]
    if not representatives:
        for i in range(0,len(joins),joins_per_module):
            js=joins[i:i+joins_per_module];module=js[0]['module'];imports=[endpoint(q[k])['module']for q in js for k in ['left','right']]
            text=header([m for m in imports if m!=module])
            for q in js:
                p=q['path'];text+=f"theorem {q['theorem']} :\n    {goal(p)} :=\n  allSites_join SitePrefix246.checkSite {bits(p[::-1])}\n    (descend ActualTree254.tree {bits(p+[False])})\n    (descend ActualTree254.tree {bits(p+[True])})\n    {endpoint(q['left'])['theorem']} {endpoint(q['right'])['theorem']}\n\n"
            unit(module,text+footer(),[q['theorem']for q in js],[goal(q['path'])for q in js],dict(kind='binary_composition',join_count=len(js)))
        rt=endpoint(root)
        text=header([rt['module']])+'''/-- Every leaf of the actual decoder has checked exact246 execution. -/
theorem all_sites : allSites SitePrefix246.checkSite [] ActualTree254.tree = true :=
  '''+rt['theorem']+'''

theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d)) :
    SitePrefix246.checkSite (consume P d) e = true :=
  allSites_walk SitePrefix246.checkSite Prog254.program ActualTree254.tree
    ActualTree254.tree_eq all_sites P e d hw

theorem actual_walk_exists (P : List Bool) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d) :=
  allSites_walk_total SitePrefix246.checkSite Prog254.program ActualTree254.tree
    ActualTree254.tree_eq all_sites P
'''+footer()
        finalaudit='''import BusyBeaver.ZFC.SitesPrefix246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.all_sites
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.actual_walk_checked
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.actual_walk_exists

example : allSites SitePrefix246.checkSite [] ActualTree254.tree = true := all_sites

example (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d)) :
    SitePrefix246.checkSite (consume P d) e = true := actual_walk_checked P e d hw

example (P : List Bool) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d) :=
  actual_walk_exists P
'''
        unit('SitesPrefix246',text,['all_sites','actual_walk_checked','actual_walk_exists'],['closed root','typed checked walk','typed total walk'],dict(kind='closed_final'),finalaudit)
    report=dict(status='GENERATED_SOURCE_ONLY_UNBUILT',compiler_or_version_called=False,tree_source_sha256=TREE_SHA,nodes=6459,leaves=6460,guard_cases=8391,decoder_depth=34,max_guards_per_cut=cap,joins_per_module=joins_per_module,max_cuts_per_module=cuts_per_module,max_batch_guards=max_batch_guards,representatives_only=representatives,isolated_cuts=sorted(isolated),chunks=len(cuts),joins=len(joins),selected_units=len(units),cut_frontier=cuts,join_plan=joins,units=units,scope='Closed actual246 tree checks and both-child joins. No omission-sensitive external premise. File grouping is source-only pending measured root execution. All3final theorem probes/typed clients included.')
    return files,report

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--max-guards',type=int,default=64);p.add_argument('--joins-per-module',type=int,default=16)
    p.add_argument('--cuts-per-module',type=int,default=1);p.add_argument('--max-batch-guards',type=int,default=64)
    p.add_argument('--representatives',action='store_true');a=p.parse_args()
    assert __debug__ and 2<=a.max_guards<=256 and 1<=a.joins_per_module<=32 and 1<=a.cuts_per_module<=16 and a.max_guards<=a.max_batch_guards<=512
    out=a.output.resolve();assert not out.is_relative_to(a.repo.resolve()) and (not out.exists()or not any(out.iterdir()))
    files,report=build_plan(a.repo,a.max_guards,a.joins_per_module,a.cuts_per_module,a.max_batch_guards,a.representatives)
    out.mkdir(parents=True,exist_ok=True)
    for n,v in files.items():(out/n).write_bytes(v)
    (out/'generation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k]for k in ['status','selected_units','representatives_only','chunks','joins','leaves','guard_cases']},indent=2))
if __name__=='__main__':main()
