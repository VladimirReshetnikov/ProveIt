#!/usr/bin/env python3
"""Static and finite-data checks only. This is NOT a Lean elaborator/kernel check."""
from pathlib import Path
import argparse, hashlib, json, re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
P=argparse.ArgumentParser(description=__doc__)
P.add_argument('--baseline','--source-root',dest='baseline',type=Path,
    help='Pinned main Lean source directory, Lean root, or full repository snapshot')
P.add_argument('--candidate',type=Path,default=HERE/'candidate/WangTiles942RowStep.lean')
P.add_argument('--output',type=Path,help='Optionally write the JSON receipt; default is stdout only')
args=P.parse_args()
def find_baseline(path):
    choices=[path,path/'DiophantineConsistency',
             path/'Lean/DiophantineConsistency',
             path/'Computability/DiophantineConsistency/Lean/DiophantineConsistency']
    return next((p for p in choices if (p/'WangTiles942RowStep.lean').is_file()),None)
roots=[args.baseline] if args.baseline else [ROOT/'baseline',ROOT/'upstream']
BASE=next((p for r in roots if (p:=find_baseline(r)) is not None),None)
if BASE is None: raise SystemExit('FAIL: pinned main Lean baseline not found; supply --baseline PATH')

def require(condition,message):
    if not condition: raise SystemExit('FAIL: '+message)

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def theorem(text,name):
    m=re.search(rf'(theorem {name}\b[\s\S]*? := by\n)([\s\S]*?)(?=\n/--|\nend )',text)
    require(m is not None,'missing declaration '+name)
    return m.group(1),m.group(2)

hashes=json.loads((HERE/'source_hashes.json').read_text())
for name,h in hashes.items(): require(digest(BASE/name)==h,'source hash mismatch '+name)
old=(BASE/'WangTiles942RowStep.lean').read_text();new=args.candidate.read_text()
old_names=re.findall(r'^theorem (\w+)',old,re.M)
for name in old_names:
    os,ob=theorem(old,name);ns,nb=theorem(new,name)
    require(os==ns,'existing statement changed '+name)
    if name not in ('far_west_zero','far_east_zero','far_pass'):
        require(ob==nb,'unrelated proof changed '+name)
for name in ('receive_at_next_head','far_pass_or_finish'):
    s,b=theorem(new,name)
    require('hTime' not in s+b,'temporal matching leaked into '+name)
    require('no_south438' not in s+b,'nonfinish leaked into '+name)
require('no_south438' in theorem(new,'far_pass')[1],'far_pass dropped derived no-finish')
require('p < 215' not in new and 'p ≠ 215' not in new,'invalid halt-target exclusion')
require(not re.search(r'\b(sorry|admit|axiom)\b',new),'unchecked proof escape')

raw=(BASE/'WangTiles942Data.lean').read_text()
cache=raw.split('def actionCache : Array Action := #[',1)[1].split('\n ]',1)[0]
actions=[(w=='true',d=='true',int(q)) for w,d,q in re.findall(r'\((true|false), (true|false), (\d+)\)',cache)]
require(len(actions)==430,'action-cache cardinality')
targets={d:sorted({q for _,dd,q in actions if dd==d}) for d in (False,True)}
require([len(targets[d]) for d in (False,True)]==[45,199],'directional targets')
def rail(d,q): return 205-199*int(d)+sum(p<q for p in targets[d])
def hc(q,b): return 2*q+b+2
# The four coordinates are WEST, NORTH, EAST, SOUTH.
def receiver(d,q,b): return (int(d)*rail(d,q),b,(1-int(d))*rail(d,q),hc(q,b))
def transition(j):
    w,d,q=actions[j]
    return ((1-int(d))*rail(False,q),j+2,int(d)*rail(True,q),int(w))
receives=[(d,q,b,receiver(d,q,b)) for d in (False,True) for q in targets[d] for b in (0,1)]
plain=[(0,b,0,b) for b in (0,1)]+[(0,b,0,438) for b in (0,1)]+[t for _,_,_,t in receives]
seams=[(a*a,437,b,437) for a in range(3) for b in range(3)]
require(len(receives)==488 and len(plain)==492,'plain/receiver cardinalities')
# These obligations are exactly what forces the incoming-side neighbor to be the old head.
matched_plain_pairs=0
for left in plain:
    for right in plain:
        if left[2]==right[0]:
            matched_plain_pairs+=1
            require(left[2]==0,'nonzero plain/plain ghost signal')
wall_checks=0
for d,q,b,t in receives:
    for wall in seams:
        wall_checks+=1
        require((wall[2]!=t[0]) if d else (t[2]!=wall[0]),'receiver fed by seam')
    require(6<=rail(d,q)<250,'rail lower/upper bound')
transition_checks=0;transition_matches=0;halt_matches=0
for j,(w,hd,hq) in enumerate(actions):
    head=transition(j)
    for d,q,b,t in receives:
        transition_checks+=1
        matches=(head[2]==t[0]) if d else (t[2]==head[0])
        if matches:
            transition_matches+=1
            require(d==hd and q==hq,'receive does not follow actual action direction/target')
            if q==215: halt_matches+=1
# Negative control 1: finishing is not excluded by plain north + zero horizontal edges.
finish=(0,0,0,438);passed=(0,0,0,0)
require(finish in plain and finish[:3]==passed[:3] and finish!=passed,
        'missing finish counterexample to over-strong plain+zero => pass')
# Negative control 2: target 215 really occurs and its receive tile has halted head color.
require(215 in targets[True] and halt_matches==2,'halt target was lost')
halt_index=next(j for j,a in enumerate(actions) if a[2]==215)
require(halt_index==125 and receiver(True,215,0)[3]==432 and receiver(True,215,1)[3]==433,
        'halt receive color/control mismatch')
# Local horizontally matching strip with an unchanged finish, illustrating the guard.
row={-3:(0,437,0,437),-2:passed,-1:finish,0:transition(halt_index),
     1:receiver(True,215,0),2:passed,3:passed,4:(0,437,0,437)}
require(all(row[x][2]==row[x+1][0] for x in range(-3,4)),'negative-control row does not match')
require(row[-1][3]==438 and row[1][3]==432,'negative-control intended outputs absent')
# Replay the exact unified patch in memory: no git metadata, external tools, or writes.
def replay_patch(source,patch):
    oldlines=source.splitlines(keepends=True)
    lines=patch.splitlines(keepends=True)
    result=[]; cursor=0; i=0; hunks=0
    while i<len(lines):
        if not lines[i].startswith('@@ '):
            i+=1; continue
        m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
        require(m is not None,'invalid unified hunk header')
        oldstart=int(m.group(1))-1
        require(oldstart>=cursor,'overlapping patch hunk')
        result.extend(oldlines[cursor:oldstart]);cursor=oldstart
        oldcount=newcount=0;i+=1;hunks+=1
        while i<len(lines) and not lines[i].startswith('@@ '):
            line=lines[i]
            if line.startswith(('--- ','+++ ')): break
            if line.startswith('\\ No newline'): i+=1;continue
            require(line[:1] in (' ','+','-'),'invalid unified patch line')
            if line[:1] in (' ','-'):
                require(cursor<len(oldlines) and oldlines[cursor]==line[1:],
                        'patch context differs from pinned source')
                cursor+=1;oldcount+=1
            if line[:1] in (' ','+'):
                result.append(line[1:]);newcount+=1
            i+=1
        require(oldcount==int(m.group(2) or 1),'old hunk count')
        require(newcount==int(m.group(4) or 1),'new hunk count')
    require(hunks>0,'patch has no hunks')
    return ''.join(result+oldlines[cursor:])
patch=(HERE/'receiver_causality.patch').read_text()
require(replay_patch(old,patch)==new,'candidate does not equal in-memory patch result')
for name,h in hashes.items(): require(digest(BASE/name)==h,'source modified '+name)
result={'result':'PASS_STATIC_AND_FINITE_ONLY','pin':'22e020937caa81d0cb72a4f63071d6c0bcc1eba9',
 'source_hashes_checked':len(hashes),'existing_statements_preserved':old_names,
 'candidate_sha256':digest(args.candidate),'action_count':len(actions),
 'receiver_count':len(receives),'plain_pair_tests':len(plain)**2,
 'matched_plain_pairs_all_zero':matched_plain_pairs,'seam_receiver_tests':wall_checks,
 'transition_receiver_tests':transition_checks,'actual_matching_receivers':transition_matches,
 'halt_receiver_matches':halt_matches,'negative_controls':{
 'plain_finish_has_zero_edges_and_plain_north':True,'halt_215_is_valid_target':True,
 'local_matching_strip_can_have_unchanged_finish_without_temporal_constraints':row},
 'patch_replay_in_memory':'PASS','lean_elaboration':'NOT RUN','lean_kernel':'NOT RUN',
 'limitations':['Finite tests authenticate local arithmetic/model obligations only, not universal Lean proofs.',
 'The local negative-control strip is not asserted to satisfy full PersistentStrip or time matching.',
 'Source snapshots are preserved; no kernel-validation or performance claim.']}
receipt=json.dumps(result,indent=2)+'\n'
if args.output is not None:
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(receipt)
print(receipt,end='')
