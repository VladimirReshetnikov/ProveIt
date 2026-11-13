#!/usr/bin/env python3
"""Read-only audit of the finite-sum selector/copy decoder join."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-943-decoder-prototype';OUT=Path('/tmp/ipra-compact943-decoder-pair-01');DIV=Path('/tmp/ipra-compact-selector-div-pair-01');WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='e0b721312d13d88ed5fadc7b83d2e8d1e95dd5a73ae559e8c40386f9b171bb4d';SOURCE='b86cef78ba82bb77e3a5c4f4c5dafeb719f7b8e802ff0527ef31dca4bc62271f';OBJECT='5de069136857ac98530c177cbcba38435569202a8e8806ff9d01f5f45950e76b';LOG='21bc49325675b912cf905824aa3cc20918aee98137a3464d46a18698e815940b'
PARENTS=[('compact44-decoder-iff','CompactDecoderIff','ipra-compact-decoder-iff-pair-01','b3f687cce2cfcd7196d36fe5f07b4d4c21c08fdef8c2e9213b41ebbbb679b533','ab243e21da873d0214b22ce3c3571df1ba8c5d8f879d870803084c32bcc7f1ff'),('compact44-943-table','Compact943Data','ipra-compact943-table-pair-01','a4efb0c47a97e78497915c891b0d76be82dc8753eb842c2d15a921f3568ff920','092cf01d0bf249e88f75c78a31eb69f15040dfe985f1e990b19b8d296b9bd9d4'),('compact44-tile-payload','CompactTilePayload','ipra-compact-tile-payload-pair-01','2b8415adc827c89f760a88b66a7ec293aeeb8d89d51511e9db7dc85304ae9c22','5ac1da28dc3f648630e0b554e90df4643e2ddaeeb84c0542f73d85b5d92e49c2')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/';names=subprocess.run(['git','ls-tree','-r','--name-only','a559988b8a','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(names)>=8,'source inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','a559988b8a:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    term=(PKG/'evidence/terminal.txt').read_text();need(term.startswith('Actual outer wrapper session 31869 exited 0. Its output was:\n') and term.endswith('PASS_PAIRED_COMPACT_943_DECODER '+RECEIPT+'\n'),'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_COMPACT_943_DECODER' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    for tag,module,run,receipt,obj in PARENTS:
        audit=BASE/'reviews'/(tag+'-independent-audit');need(sha(audit/'CHECK.json')==receipt,'parent audit receipt '+tag)
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((audit/'CHECK.json').read_bytes()),'parent audit rerun '+tag)
    win=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit/CHECK.json';need(r['parent_audit']==json.loads(win.read_bytes()),'shared parent receipt')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;lib=run/'lib';src=run/'src/Compact943Decoder.lean';obj=run/'Compact943Decoder.olean';log=run/'compiler.log';parent=Path('/tmp/ipra-compact-decoder-iff-pair-01')/side/'lib';window=Path('/tmp/ipra-compact-selector-decoder-pair-01')/side/'lib'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded exits')
        need(sha(src)==sha(PKG/'Compact943Decoder.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and row['stdout']==log.read_text(),'logs')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        parentfiles={p.relative_to(parent) for p in parent.rglob('*.olean')};windowfiles={p.relative_to(window) for p in window.rglob('*.olean')};files={p.relative_to(lib) for p in lib.rglob('*.olean')}
        extra={Path('DiophantineConsistency')/(x+'.olean') for x in ('CompactSelectorDecoder','CompactSelectorConverse')};seeds={Path('DiophantineConsistency')/(x[1]+'.olean') for x in PARENTS}
        need(parentfiles==windowfiles|extra and files==parentfiles|seeds and not(parentfiles&seeds),'overlay membership')
        for rel in parentfiles:need((lib/rel).resolve()==(parent/rel).resolve() and sha(lib/rel)==sha(parent/rel),'parent overlay '+str(rel))
        for rel in windowfiles:need(sha(parent/rel)==sha(window/rel),'window '+str(rel))
        need(sha(window/'DiophantineConsistency/CompactSelector.olean')=='da6845b6426d5f6673facc34f7a2b840cd174202360dc2df67984ba84a6442f9','selector seed')
        for tag,module,prun,receipt,h in PARENTS:
            seed=lib/'DiophantineConsistency'/(module+'.olean');need(sha(seed)==sha(Path('/tmp')/prun/side/(module+'.olean'))==row['seed_sha256'][module]==h,'seed '+module)
        deps={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(x[1]+'.olean')) for x in PARENTS}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct dependencies')
        expected="".join("'Compact943Decoder."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('tileValue_bounds','count_bound','decode_iff'))
        need(row['stdout']==expected and row['axiom_reports']==[['Compact943Decoder.'+n,'propext, Classical.choice, Quot.sound'] for n in ('tileValue_bounds','count_bound','decode_iff')],'reports')
        summaries.append({'side':side,'object_sha256':OBJECT,'parent_overlay_objects':len(parentfiles),'added_parent_seeds':3,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_943_DECODER_AUDIT','source_commit':'a559988b8a','author_receipt_sha256':RECEIPT,'recorded_outer_session':31869,'recorded_outer_exit':0,'parent_audit_rerun_exits':[0,0,0],'runs':summaries,'scope':'Conditional external Fin 943 model decoder equivalence; selector and W bounds are assumptions, not obtained from graph. No 943-tile binding, checker calibration, iPRA proof or complete provider axiom inventory.'},indent=2))
if __name__=='__main__':main()
