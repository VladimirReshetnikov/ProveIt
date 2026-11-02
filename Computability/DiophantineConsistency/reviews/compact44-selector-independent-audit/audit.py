#!/usr/bin/env python3
"""Read-only audit of the conditional compact selector-count suffix."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-selector-prototype'
OUT=Path('/tmp/ipra-compact-selector-pair-01')
PARENT=Path('/tmp/ipra-thirteen-parent-window-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit'
RECEIPT='b2c50f1f34070e10a13d28f3cc84fe473f4f0f8d3e1d2e38dbbac08f3ad012b3'
SOURCE='4a85f7f526cbc2aef8b97c3246a5a10e13be705ae32e1a70a3221043a42fcc06'
OBJECT='da6845b6426d5f6673facc34f7a2b840cd174202360dc2df67984ba84a6442f9'
LOG='a60142b3bc68be164f41774f06dc7640f2b253e77760ccd53557bb822edac008'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    names=('README.md','CompactSelector.lean','replay.py','evidence/receipt.json','evidence/terminal.txt','evidence/author.log','evidence/peer.log','observations/attempt01.lean','observations/attempt01.log','observations/attempt02.log','observations/attempts.txt')
    for name in names:
        p=PKG/name;b=subprocess.run(['git','show','bea685c46d:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    need((PKG/'evidence/terminal.txt').read_text()==f'Actual outer wrapper session 11053 exited 0. Its output was:\nauthor exit 0 peak_RSS 1762250752\npeer exit 0 peak_RSS 1761984512\nPASS_PAIRED_COMPACT_SELECTOR_COUNT {RECEIPT}\n','terminal')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_COMPACT_SELECTOR_COUNT' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(AUDIT/'CHECK.json')=='4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9','parent receipt hash')
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent,'recorded parent receipt')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;src=run/'src/CompactSelector.lean';obj=run/'CompactSelector.olean';log=run/'compiler.log'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded exits')
        need(sha(src)==sha(PKG/'CompactSelector.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source and object')
        need(sha(log)==sha(PKG/('evidence/'+side+'.log'))==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        deps={str(PACKAGE/'Init.olean'),str(PARENT/side/'lib/DiophantineConsistency/ArithmeticWindowDigits.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(q).is_file() for q in deps),'direct deps')
        need(row['stdout']=="'CompactSelector.selector_at_most_one' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and row['axiom_reports']==['propext, Classical.choice, Quot.sound'],'report')
        summaries.append({'side':side,'object_sha256':OBJECT,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    need('sorryAx' in (PKG/'observations/attempt01.log').read_text() and 'warning:' not in (PKG/'observations/attempt02.log').read_text() and 'sorryAx' not in (PKG/'observations/attempt02.log').read_text(),'exploratory logs')
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_SELECTOR_AUDIT','source_commit':'bea685c46d','author_receipt_sha256':RECEIPT,'recorded_outer_session':11053,'recorded_outer_exit':0,'parent_audit_rerun_exit':p.returncode,'runs':summaries,'scope':'Conditional model bound n≤1 from n<2^10 and explicit NoCarry hypothesis for arbitrary P; no payload binding, checker calibration, iPRA proof, complete parent axiom inventory or transitive provider claim.'},indent=2))
if __name__=='__main__':main()
