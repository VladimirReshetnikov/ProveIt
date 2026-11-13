#!/usr/bin/env python3
"""Read-only artifact audit of a conditional compact decoder parent."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
CONFIG = {'tag': 'compact44-structured-mask', 'commit': '0f06df0a20', 'module': 'CompactStructuredMask', 'session': 87641, 'receipt': 'a0a44a8e776f47d5ef511fdbf631b12c9558c040e2744856c6ce67815f4435b5', 'status': 'PASS_PAIRED_COMPACT_STRUCTURED_MASK', 'source': '9ed69e88d795fc67c5e95a4317e184f6547236bf2b6d6b289ce0f6c5a5b98715', 'obj': 'b9d9ce419455247cdf7b8e5f3e801f551eba676d0fe9af5e7579e40e048f1b85', 'log': 'fd4e710afdcc4f1222729858ad00b3dd5e76dadd57be5ea11eed1448af723fd9', 'reports': ['structured_exact_block', 'standard_blocks_exists', 'structured_block'], 'out': 'ipra-compact-structured-mask-pair-01', 'seed': False}
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge'/(CONFIG['tag']+'-prototype')
OUT=Path('/tmp')/CONFIG['out']
WINDOW=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/'
    names=subprocess.run(['git','ls-tree','-r','--name-only',CONFIG['commit'],'--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(names)>=11,'committed inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show',CONFIG['commit']+':'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    terminal=(PKG/'evidence/terminal.txt').read_text()
    need(terminal.startswith('Observed outer session '+str(CONFIG['session'])+' exit 0.\n') and terminal.endswith(CONFIG['status']+' '+CONFIG['receipt']+'\n'),'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==CONFIG['receipt'],'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes());need(r['status']==CONFIG['status'] and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent and sha(AUDIT/'CHECK.json')=='50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce','parent receipt')
    audit=BASE/'reviews'/('compact44-selector-independent-audit' if CONFIG['seed'] else 'thirteen-model-endpoint-successor-pair-independent-audit')
    q=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],capture_output=True,timeout=900)
    need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((audit/'CHECK.json').read_bytes()),'parent audit rerun')
    results=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side; src=Path(row['command'][-3]); obj=run/(CONFIG['module']+'.olean'); log=run/'compiler.log'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded exits')
        need(sha(src)==sha(PKG/(CONFIG['module']+'.lean'))==row['source_sha256']==CONFIG['source'] and sha(obj)==row['object_sha256']==CONFIG['obj'],'source/object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==CONFIG['log'] and log.read_text()==row['stdout'],'compiler log')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        if CONFIG['seed']:
            lib=run/'lib';win=WINDOW/side/'lib';seed=lib/'DiophantineConsistency/CompactSelector.olean'
            wf={p.relative_to(win) for p in win.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
            need(lf==wf|{Path('DiophantineConsistency/CompactSelector.olean')},'overlay inventory')
            for rel in wf:need((lib/rel).resolve()==(win/rel).resolve() and sha(lib/rel)==sha(win/rel),'overlay '+str(rel))
            need(sha(seed)==sha(Path('/tmp/ipra-compact-selector-pair-01')/side/'CompactSelector.olean')==row['seed_sha256']=='da6845b6426d5f6673facc34f7a2b840cd174202360dc2df67984ba84a6442f9','selector seed')
            deps={str(PACKAGE/'Init.olean'),str(seed)}
        else:
            lib=run/'lib';win=WINDOW/side/'lib';wf={p.relative_to(win) for p in win.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
            need(lf==wf,'overlay inventory')
            for rel in wf:need((lib/rel).resolve()==(win/rel).resolve() and sha(lib/rel)==sha(win/rel),'overlay '+str(rel))
            deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ArithmeticPackingBlocks.olean'),str(lib/'DiophantineConsistency/ArithmeticBinaryPopulation.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct dependencies')
        found=re.findall(r"^'"+CONFIG['module']+r"\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in found]==CONFIG['reports'] and [a for _,a in found]==['propext, Classical.choice, Quot.sound']*len(found) and row['axiom_reports']==[[CONFIG['module']+'.'+n,a] for n,a in found] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        results.append({'side':side,'source_sha256':CONFIG['source'],'object_sha256':CONFIG['obj'],'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_'+CONFIG['tag'].replace('-','_').upper()+'_AUDIT','source_commit':CONFIG['commit'],'author_receipt_sha256':CONFIG['receipt'],'recorded_outer_session':CONFIG['session'],'recorded_outer_exit':0,'parent_audit_rerun_exit':q.returncode,'runs':results,'scope':'Read-only paired artifact audit of conditional model lemmas; no graph premises, payload binding, checker calibration, complete provider axiom inventory, or iPRA proof.'},indent=2))
if __name__=='__main__':main()
