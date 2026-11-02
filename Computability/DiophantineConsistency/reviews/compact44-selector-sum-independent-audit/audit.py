#!/usr/bin/env python3
"""Read-only artifact audit of a conditional compact decoder parent."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
CONFIG = {'tag': 'compact44-selector-sum', 'commit': 'bd82dfcc4a', 'module': 'CompactSelectorSum', 'session': 66799, 'receipt': '5a06980410fcf4f0305e4f9f1c5a9ba51b399ebe0bd93a99ea80722d84f52063', 'status': 'PASS_PAIRED_COMPACT_SELECTOR_SUM', 'source': '814259bc45d143dca0e4c310c02c1f0a26dba27294dc6dcdf4d0f032ba661a5f', 'obj': '54b8e94bcc3ae1ccc97e3dc77b75394b426a97cdef98780e2c791f0b8cceceb8', 'log': '3d0df7e524cbd035b74329ec1432a39a3f203fc5ce0468740eedbe92c259d0e0', 'reports': ['sum_le_one_cases', 'selected_weighted'], 'out': 'ipra-compact-selector-sum-pair-01', 'seed': False}
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge'/(CONFIG['tag']+'-prototype')
OUT=Path('/tmp')/CONFIG['out']
WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit'
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
    need(terminal.startswith('Actual outer wrapper session '+str(CONFIG['session'])+' exited 0. Its output was:\n') and terminal.endswith(CONFIG['status']+' '+CONFIG['receipt']+'\n'),'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==CONFIG['receipt'],'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes());need(r['status']==CONFIG['status'] and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent and sha(AUDIT/'CHECK.json')=='4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9','parent receipt')
    audit=BASE/'reviews'/('compact44-selector-independent-audit' if CONFIG['seed'] else 'thirteen-model-parent-window-pair-independent-audit')
    q=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],capture_output=True,timeout=180)
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
        else: deps={str(PACKAGE/'Init.olean'),str(WINDOW/side/'lib/DiophantineConsistency/ArithmeticWindowDigits.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct dependencies')
        found=re.findall(r"^'"+CONFIG['module']+r"\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in found]==CONFIG['reports'] and [a for _,a in found]==['propext, Classical.choice, Quot.sound']*len(found) and row['axiom_reports']==[a for _,a in found] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        results.append({'side':side,'source_sha256':CONFIG['source'],'object_sha256':CONFIG['obj'],'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_'+CONFIG['tag'].replace('-','_').upper()+'_AUDIT','source_commit':CONFIG['commit'],'author_receipt_sha256':CONFIG['receipt'],'recorded_outer_session':CONFIG['session'],'recorded_outer_exit':0,'parent_audit_rerun_exit':q.returncode,'runs':results,'scope':'Read-only paired artifact audit of conditional model lemmas; no graph premises, payload binding, checker calibration, complete provider axiom inventory, or iPRA proof.'},indent=2))
if __name__=='__main__':main()
