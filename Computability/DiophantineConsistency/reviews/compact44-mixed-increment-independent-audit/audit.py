#!/usr/bin/env python3
"""Read-only paired mixed-mask provider and theorem artifact audit."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
CONFIG = {'tag': 'compact44-mixed-increment', 'commit': '116ab88a4c', 'module': 'CompactMixedIncrement', 'session': 49860, 'receipt': '64e8b41aed059ed22bb836e4fc3456aa1f05fedb9191c4062784b9c31eb3e7de', 'status': 'PASS_PAIRED_COMPACT_MIXED_INCREMENT', 'source': '056b203e0b207fb9f88893828df4d721a4aff3106fd85c503285470de9cd713d', 'obj': '23786f0922f76f0a45b4a86feb3f08361000b35ca25c502d5e6c100b5b706f94', 'log': 'ec9e3881125d54848282f6747cd035f2f2dd809ecbca5aeecc6da8bb988d26d8', 'reports': ['decode_mixed_increment'], 'out': 'ipra-compact-mixed-increment-pair-01', 'deps': ['CompactMaskSlot', 'ArithmeticWindowBits'], 'parents': [('compact44-dummy-bound', 'CompactDummyBound', 'ipra-compact-dummy-bound-pair-01', 'a2a144c733e6a1fee23e07025f95755168000c4b4f538e3911e9d29f5f26052e', '188bf0f06d92cc171c3eb712cced46ac44cae65ae32e4891333646342d46ce38'), ('compact44-mask-slot', 'CompactMaskSlot', 'ipra-compact-mask-slot-pair-01', '7ee25fa5ad3fc966b78491325b2ad2f30c2e0b7a205ddd0e33e23a39d2d68168', 'a3dbd600d24333b4c6d5d454b21e532d9e8badce03f9293198a2823caae9cc5f')]}
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge'/(CONFIG['tag']+'-prototype');OUT=Path('/tmp')/CONFIG['out'];WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/';names=subprocess.run(['git','ls-tree','-r','--name-only',CONFIG['commit'],'--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len(names)>=9,'packet inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show',CONFIG['commit']+':'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    term=(PKG/'evidence/terminal.txt').read_text();need(term.startswith('Observed outer session '+str(CONFIG['session'])+' exit 0.\n') and term.endswith(CONFIG['status']+' '+CONFIG['receipt']+'\n'),'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==CONFIG['receipt'],'receipt');r=json.loads((PKG/'evidence/receipt.json').read_bytes());need(r['status']==CONFIG['status'] and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    for tag,module,run,receipt,obj in CONFIG['parents']:
        audit=BASE/'reviews'/(tag+'-independent-audit');need(sha(audit/'CHECK.json')==receipt,'parent receipt '+tag)
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],capture_output=True,timeout=180);need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((audit/'CHECK.json').read_bytes()),'parent audit rerun '+tag)
    win=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit/CHECK.json';need(r['parent_audit']==json.loads(win.read_bytes()),'shared parent')
    results=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;lib=run/'lib';window=WINDOW/side/'lib';src=Path(row['command'][-3]);obj=run/(CONFIG['module']+'.olean');log=run/'compiler.log'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded exits')
        need(sha(src)==sha(PKG/(CONFIG['module']+'.lean'))==row['source_sha256']==CONFIG['source'] and sha(obj)==row['object_sha256']==CONFIG['obj'],'source/object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==CONFIG['log'] and log.read_text()==row['stdout'],'log')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        wf={p.relative_to(window) for p in window.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')};seeds={Path('DiophantineConsistency')/(x[1]+'.olean') for x in CONFIG['parents']}
        need(lf==wf|seeds and not(wf&seeds),'overlay inventory')
        for rel in wf:need((lib/rel).resolve()==(window/rel).resolve() and sha(lib/rel)==sha(window/rel),'window overlay '+str(rel))
        for tag,module,prun,receipt,h in CONFIG['parents']:
            seed=lib/'DiophantineConsistency'/(module+'.olean');need(sha(seed)==sha(Path('/tmp')/prun/side/(module+'.olean'))==row['seed_sha256'][module]==h,'seed '+module)
        deps={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(n+'.olean')) for n in CONFIG['deps']};need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct dependencies')
        found=re.findall(r"^'"+CONFIG['module']+r"\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M);need([n for n,_ in found]==CONFIG['reports'] and [a for _,a in found]==['propext, Classical.choice, Quot.sound']*len(found) and row['axiom_reports']==[[CONFIG['module']+'.'+n,a] for n,a in found] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        results.append({'side':side,'object_sha256':CONFIG['obj'],'window_objects':len(wf),'added_seeds':len(seeds),'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_'+CONFIG['tag'].replace('-','_').upper()+'_AUDIT','source_commit':CONFIG['commit'],'author_receipt_sha256':CONFIG['receipt'],'recorded_outer_session':CONFIG['session'],'recorded_outer_exit':0,'parent_audit_rerun_exits':[0]*len(CONFIG['parents']),'runs':results,'scope':'Conditional model mixed-mask arithmetic with explicit hypotheses; no concrete graph/temporal alignment, checker calibration, iPRA proof or complete provider ancestry.'},indent=2))
if __name__=='__main__':main()
