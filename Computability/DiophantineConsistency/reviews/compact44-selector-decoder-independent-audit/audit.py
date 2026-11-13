#!/usr/bin/env python3
"""Read-only audit of the finite-sum selector/copy decoder join."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-selector-decoder-prototype';OUT=Path('/tmp/ipra-compact-selector-decoder-pair-01');DIV=Path('/tmp/ipra-compact-selector-div-pair-01');WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='6089c57318e1156c0b110185ec535d65e4193739575441fc168248c587524180';SOURCE='96ba4a6ca5855ec86698b1f7fb2fecf4deeeb4fe5df04bb923cc0203242fe970';OBJECT='e66d0eb6274ae20a59dae67485e4c5a8832a4b01a8e00e3d550b190ca2263faf';LOG='997a1ef4a9c992b9f17e360294ee8979c28d2c7c99bdc25ac7da6522bf764a88'
PARENTS=[('compact44-selector-div','CompactSelectorDiv','ipra-compact-selector-div-pair-01','11f1729d1dfce570819198a6e2abccb4cf64df4a3f801a11570e74736efc575c','21093436635a66d7db04d80af4324ebe3234f9202548870aba57f8849fa0580a'),('compact44-copy','CompactCopy','ipra-compact-copy-pair-01','2be7111fe2d8423681bf473e50a40f3738e4c2a75aa6cf3ed98681dd88e80bc2','e8e06f23d7e6b25f6aad9e2ba354df92f9fc9d21b1fa6d404468a857234aa955'),('compact44-selector-sum','CompactSelectorSum','ipra-compact-selector-sum-pair-01','b264e7f68896ecba2564ea62344958b5b51d3e47bb1ecade9b7cc3570d8f125d','54b8e94bcc3ae1ccc97e3dc77b75394b426a97cdef98780e2c791f0b8cceceb8')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/';names=subprocess.run(['git','ls-tree','-r','--name-only','2ad42e3c7d','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(names)>=8,'source inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','2ad42e3c7d:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    term=(PKG/'evidence/terminal.txt').read_text();need(term.startswith('Actual outer wrapper session 63674 exited 0. Its output was:\n') and term.endswith('PASS_PAIRED_COMPACT_SELECTOR_DECODER '+RECEIPT+'\n'),'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_COMPACT_SELECTOR_DECODER' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    for tag,module,run,receipt,obj in PARENTS:
        audit=BASE/'reviews'/(tag+'-independent-audit');need(sha(audit/'CHECK.json')==receipt,'parent audit receipt '+tag)
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((audit/'CHECK.json').read_bytes()),'parent audit rerun '+tag)
    win=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit/CHECK.json';need(r['parent_audit']==json.loads(win.read_bytes()),'shared parent receipt')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;lib=run/'lib';src=run/'src/CompactSelectorDecoder.lean';obj=run/'CompactSelectorDecoder.olean';log=run/'compiler.log';parent=DIV/side/'lib';window=WINDOW/side/'lib'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded exits')
        need(sha(src)==sha(PKG/'CompactSelectorDecoder.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and row['stdout']==log.read_text(),'logs')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        parentfiles={p.relative_to(parent) for p in parent.rglob('*.olean')};windowfiles={p.relative_to(window) for p in window.rglob('*.olean')};files={p.relative_to(lib) for p in lib.rglob('*.olean')}
        extra=Path('DiophantineConsistency/CompactSelector.olean');seeds={Path('DiophantineConsistency')/(x[1]+'.olean') for x in PARENTS}
        need(parentfiles==windowfiles|{extra} and files==parentfiles|seeds and not(parentfiles&seeds),'overlay membership')
        for rel in parentfiles:need((lib/rel).resolve()==(parent/rel).resolve() and sha(lib/rel)==sha(parent/rel),'parent overlay '+str(rel))
        for rel in windowfiles:need(sha(parent/rel)==sha(window/rel),'window '+str(rel))
        need(sha(parent/extra)=='da6845b6426d5f6673facc34f7a2b840cd174202360dc2df67984ba84a6442f9','selector seed')
        for tag,module,prun,receipt,h in PARENTS:
            seed=lib/'DiophantineConsistency'/(module+'.olean');need(sha(seed)==sha(Path('/tmp')/prun/side/(module+'.olean'))==row['seed_sha256'][module]==h,'seed '+module)
        deps={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(x[1]+'.olean')) for x in PARENTS}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct dependencies')
        need(row['stdout']=="'CompactSelectorDecoder.decode' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and row['axiom_reports']==['propext, Classical.choice, Quot.sound'],'report')
        summaries.append({'side':side,'object_sha256':OBJECT,'parent_overlay_objects':len(parentfiles),'added_parent_seeds':3,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_SELECTOR_DECODER_AUDIT','source_commit':'2ad42e3c7d','author_receipt_sha256':RECEIPT,'recorded_outer_session':63674,'recorded_outer_exit':0,'parent_audit_rerun_exits':[0,0,0],'runs':summaries,'scope':'Conditional model finite-index decoder only; assumptions are explicit, not obtained from graph. No 943-tile binding, checker calibration, iPRA proof or complete provider axiom inventory.'},indent=2))
if __name__=='__main__':main()
