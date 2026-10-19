#!/usr/bin/env python3
"""Seek exact symbolic entry collisions before a proposed free return126/read0.
Candidate collision diagnostics; register realizability and target incompatibility
need separate proof before this can become an obstruction theorem.
"""
from pathlib import Path
import os,sys,json,importlib.util,collections
H=Path(__file__).resolve().parent;R=H.parent/'context_folds';os.environ['ZFC246_BASE']=str(R/'recovered/63');os.environ['ZFC246_TABLE']=str(R/'recovered/63/machine/zfc_prefix246_old.tm')
spec=importlib.util.spec_from_file_location('f',R/'recovered/64/experiments/decoder/fold_search246.py');f=importlib.util.module_from_spec(spec);sys.modules['f']=f;spec.loader.exec_module(f)
src=(R/'recovered/63/sources/prior/prefix_affine.py').read_text();src=src.replace("if seg[0]=='b':\n            write,move,following=table[q,seg[1]]", "if seg[0]=='b':\n            if q=='126' and seg[1]==0: return ('boundary',canon(left,right))\n            write,move,following=table[q,seg[1]]")
ns={};exec(compile(src,'boundary_affine','exec'),ns)
t={k:v for k,v in f.T.items()if k[0]!='255'};t['75',0]=(0,'R','63');t['48',0]=(1,'L','131');t['131',0]=(1,'L','126')
groups=collections.defaultdict(list);errors=collections.Counter()
def strip_effect(s):
 if isinstance(s,tuple):
  if len(s)==2 and s[0]=='box' and s[1][0]=='plain':return ('box',('plain',None))
  return tuple(strip_effect(x)for x in s)
 return s
for i,(pc,op,r,z,guard,target) in enumerate(f.CASES):
 tr=f.Tracking(t)
 try:out=ns['run'](tr,pc,guard,target,halt=op=='CH',fuel=2000)
 except(AssertionError,KeyError):errors['unsupported']+=1;continue
 if out[0]!='boundary':errors['returned_without_boundary']+=1;continue
 # A source-repair at108/0 must not alter the pre-boundary run.
 if ('108',0)in tr.used:errors['108_dependent']+=1;continue
 groups[strip_effect(out[1])].append(dict(case=i,pc=pc,op=op,r=r,zero=z,boundary=out[1],target=target))
collisions=[]
for key,rows in groups.items():
 targets={str(strip_effect(x['target']))for x in rows}
 if len(targets)>1:collisions.append(dict(shape=key,rows=rows))
report=dict(scope='Symbolic pre126 collisions, with matching file effects not yet proved realizable',groups=len(groups),errors=errors,collision_groups=len(collisions),collisions=collisions)
(H/'borrowed_tail_collision.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='collisions'},indent=2))
if collisions:print(json.dumps(collisions[0],indent=2)[:4500])
