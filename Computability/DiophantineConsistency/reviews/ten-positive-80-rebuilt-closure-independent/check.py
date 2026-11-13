#!/usr/bin/env python3
"""Verify saved rebuilt-union header batches/closure and selected companions; no Lean replay."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import json
D=Path(__file__).resolve().parents[2];A=D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01';S=A/'result.json';RUN=D/'research/ten-positive-80-coherent-rebuild/observations/attempt04';OLD=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json';BASE=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
def need(c,m):
 if not c:raise RuntimeError(m)
need(sha(S)=='75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276','scan pin')
x=j(S);r=j(RUN/'result.json');old=j(OLD);base=j(BASE);init=j(RUN/'initial-project.json');outs=j(RUN/'outside-baseline.json');union=Path(x['union']);headers=x['headers'];project=x['selected_project'];outside=x['selected_outside']
need(x['status']=='PASS' and r['status']=='PASS' and union==Path(r['output_root'])/'lib','status/union')
for path,digest in x['inputs'].items():need(sha(path)==digest,'pinned input '+path)
need(len(project)==len(headers)==len(init)==1765 and len(outside)==len(outs)==80 and len(x['batches'])==28,'counts')
reference={n:base['post_headers']['project'][n]['imports'] for n in init if n in base['post_headers']['project']};reference.update(old['fresh_headers']);need(headers==reference,'header baseline mismatch')
def verify(parts,expected,stem):
 for ext,entry in expected.items():
  rec=parts[ext];q=Path(str(stem)+ext);need(q.is_file()==(entry is not None)==(rec is not None),'presence '+str(q))
  if rec is not None:need(rec['path']==str(q) and str(q.resolve())==rec['real_path'] and sha(q)==rec['sha256']==entry['sha256'],'file '+str(q))
for n,parts in project.items():verify(parts,r['built'].get(n,init[n]),union/n.replace('.','/'))
pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');system=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for n,parts in outside.items():
 expect=outs[n];stem=Path(expect['.olean']['path'][:-6]);verify(parts,expect,stem);rel=Path(n.replace('.','/')+'.olean')
 need(not (union/rel).is_file(),'outside shadow '+n);sel=next((q/rel for q in (pack,system) if (q/rel).is_file()),None);need(sel is not None and str(sel)==parts['.olean']['path'],'outside selection '+n)
# Reparse all retained reader outputs and bind each path to the captured per-object imports.
found={}
for k,b in enumerate(x['batches']):
 so=A/f'header-{k:03d}.stdout';se=A/f'header-{k:03d}.stderr';need(b['exit']==0 and not se.read_text(),'batch failed')
 need(b['preflight']['mem_available_kib']>=8*1024**2 and len(b['preflight']['lean'])<2,'batch preflight')
 need(b['command'][1:5]==['-M3000','-j1','-DElab.async=false','--run'] and Path(b['command'][5]).name=='ReadObjectImports.lean','header command flags')
 paths=b['command'][6:];need(0<len(paths)<=64,'header chunk size');mapping={str(union/(n.replace('.','/')+'.olean')):n for n in headers};need(all(q in mapping for q in paths),'batch path')
 cur=None
 for line in so.read_text().splitlines():
  if line.startswith('BEGIN '):
   path=line[6:];need(cur is None and path in paths and mapping[path] not in found,'header begin');cur=mapping[path];found[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:found[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise RuntimeError('malformed reader output')
 need(cur is None,'unclosed header');print('batch',k,'stdout_sha256',sha(so),'stderr_sha256',sha(se))
need(found==headers,'reader logs differ from saved header graph')
todo=deque(['Direct80SymbolicFixedIPRA']);seen=set();ext=set()
while todo:
 n=todo.popleft()
 if n in seen or n in ext:continue
 if n not in headers:ext.add(n);continue
 seen.add(n);todo.extend(headers[n])
need(seen==set(project) and ext==set(outside),'reachability mismatch')
print('PASS 1765 selected project headers/companions, 80 outside leaves/companions, 28 reader batches and full reachability')
print('result',sha(S),'captured author header reads; no independent Lean replay, unrebuilt/package/dynamic history inherited')
