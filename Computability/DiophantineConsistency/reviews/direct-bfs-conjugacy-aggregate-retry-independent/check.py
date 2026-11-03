#!/usr/bin/env python3
"""Static retry comparison and failed attempt receipt check; no Lean replay."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];R=D/'research';O=R/'direct-bfs-lean-conjugacy-aggregate-prototype';N=R/'direct-bfs-lean-conjugacy-aggregate-retry-prototype';F=O/'observations/directbfsaggregate-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=(O/'DirectBFSCoverageAggregate.lean').read_text();b=(N/'DirectBFSCoverageAggregate.lean').read_text();old="    simp only [List.range'_append_1, Nat.reduceAdd]";new='    decide'
assert sha(O/'DirectBFSCoverageAggregate.lean')=='0a4d0212368891e0a3b81b030a608dbe14274d40c3a7895e66fa49f55f8ec9fe'
assert a.count(old)==7 and b==a.replace(old,new) and sha(N/'DirectBFSCoverageAggregate.lean')=='3439657a35a3817564113158e9a4b155a19e7801b725ea2bfe4eda7d23bda47b'
assert not re.search(r'\b(?:sorry|admit)\b',b)
oldrun=(O/'run-v2.py').read_text(); newrun=(N/'run.py').read_text()
oldrun=oldrun.replace("('directbfsaggregate-'+a)","('directbfsaggregateretry-'+a)").replace('0a4d0212368891e0a3b81b030a608dbe14274d40c3a7895e66fa49f55f8ec9fe','3439657a35a3817564113158e9a4b155a19e7801b725ea2bfe4eda7d23bda47b').replace("prefix='direct-bfs-aggregate-'","prefix='direct-bfs-aggregate-retry-'")
assert oldrun==newrun and sha(N/'run.py')=='1bc094f1934b8df7b54f0e7bfbadfba8c2b95cc30c0038dca5c5952761e705ef'
t=json.loads((F/'terminal.json').read_text());logs=(F/'stdout').read_text()+(F/'stderr').read_text()
assert t['exit']!=0 and sha(F/'stdout')==t['stdout_sha256'] and sha(F/'stderr')==t['stderr_sha256']
assert len(re.findall(r'error: `simp` made no progress',logs))==7 and logs.count('sorryAx')>=7
print('PASS exact seven tactic-only changes; retry source',sha(N/'DirectBFSCoverageAggregate.lean'),'runner',sha(N/'run.py'))
print('failed attempt receipt',sha(F/'terminal.json'),'Lean exit',t['exit'],'seven errors and sorryAx confirmed')
print('No Lean replay, no successful aggregate assertion; runner terminal predates final acceptance guards.')
