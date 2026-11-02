#!/usr/bin/env python3
"""Read-only paired mixed-mask provider and theorem artifact audit."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
CONFIG = {'tag': 'compact44-mask-carry-join', 'commit': '87f2fab0e1', 'module': 'CompactMaskToCarry', 'session': 1404, 'receipt': 'eb643c09c13492cd2f5a9064015bed94f6b15d9d776cb11e8332332e8b25a6c4', 'status': 'PASS_PAIRED_COMPACT_MASK_CARRY_JOIN', 'source': '738a38a25b0afc76aa0f02fa24040068d4964ea431ec0a88060056c79abef212', 'obj': '3088e8b5769b98188dfbb444894574f1c9c3f90ec80066251b2bfda580a73b5e', 'log': '66d0533c45552e9aff71d995aa8a5302da3595182f19d25d54a11be746ba443d', 'reports': ['repeated_mask_class', 'repeated_mask_digit_le_three', 'digit_le_three_of_mask', 'carry_input_of_mask'], 'out': 'ipra-compact-mask-carry-join-pair-01', 'deps': ['CompactScaledCarry', 'CompactMaskSlot'], 'parents': [('compact44-dummy-bound', 'CompactDummyBound', 'ipra-compact-dummy-bound-pair-01', 'a2a144c733e6a1fee23e07025f95755168000c4b4f538e3911e9d29f5f26052e', '188bf0f06d92cc171c3eb712cced46ac44cae65ae32e4891333646342d46ce38'), ('compact44-mask-slot', 'CompactMaskSlot', 'ipra-compact-mask-slot-pair-01', '7ee25fa5ad3fc966b78491325b2ad2f30c2e0b7a205ddd0e33e23a39d2d68168', 'a3dbd600d24333b4c6d5d454b21e532d9e8badce03f9293198a2823caae9cc5f'), ('compact44-scaled-carry', 'CompactDigitBound', 'ipra-compact-scaled-carry-pair-01', 'd2352465b3c539902040aea3f9ef189f0930cd10b1ddf3b8306444720c5a03bc', '02e49f7e1a13bbc33859c203b5e93a91a16fadf2bb1d3e8d292ab29963cc4102'), ('compact44-scaled-end-around', 'CompactScaledCarry', 'ipra-compact-scaled-end-around-pair-01', '6799ed6fc3574187c21854a73e38c52af03708eb41bb103d8f9af6c79200f4ef', '0c2cf249913dd6680baaa39a3baf4615a92d3c92f8c8b9e0096b99651da1477f')]}
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
