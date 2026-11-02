#!/usr/bin/env python3
"""Read-only audit of the finite-sum selector/copy decoder join."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-decoder-iff-prototype';OUT=Path('/tmp/ipra-compact-decoder-iff-pair-01');DIV=Path('/tmp/ipra-compact-selector-div-pair-01');WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='7fdb96e86f0ac5503b68f616fd45591c5d299767e18896704ddbe7811319ad7d';SOURCE='10b6636d29e19d2171035537d14bf8d709b7643ff2c0a71bc4ab490355832962';OBJECT='ab243e21da873d0214b22ce3c3571df1ba8c5d8f879d870803084c32bcc7f1ff';LOG='2ed989bf4992182f43efd367e9427f3a1257108e73ab622e4203f5ef9bc3fddc'
PARENTS=[('compact44-selector-decoder','CompactSelectorDecoder','ipra-compact-selector-decoder-pair-01','fa8ddafe2fc18e2ef6a77e8687e997bdf53b04cd800574c15958eb8171168db5','e66d0eb6274ae20a59dae67485e4c5a8832a4b01a8e00e3d550b190ca2263faf'),('compact44-mask-converse','CompactSelectorConverse','ipra-compact-mask-converse-pair-01','c4b48496a938ae1de146c8ab3290963f31ec6fcd4c38135778be0e8188f6f602','12c089c9903c9a3e391edd9caaadca831dca0d9933c2aacbeec4d0e331a67b13')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/';names=subprocess.run(['git','ls-tree','-r','--name-only','842f77f47a','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(names)>=8,'source inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','842f77f47a:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    term=(PKG/'evidence/terminal.txt').read_text();need(term.startswith('Actual outer wrapper session 22578 exited 0. Its output was:\n') and term.endswith('PASS_PAIRED_COMPACT_DECODER_IFF '+RECEIPT+'\n'),'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_COMPACT_DECODER_IFF' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    for tag,module,run,receipt,obj in PARENTS:
        audit=BASE/'reviews'/(tag+'-independent-audit');need(sha(audit/'CHECK.json')==receipt,'parent audit receipt '+tag)
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((audit/'CHECK.json').read_bytes()),'parent audit rerun '+tag)
    win=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit/CHECK.json';need(r['parent_audit']==json.loads(win.read_bytes()),'shared parent receipt')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;lib=run/'lib';src=run/'src/CompactDecoderIff.lean';obj=run/'CompactDecoderIff.olean';log=run/'compiler.log';parent=Path('/tmp/ipra-compact-selector-decoder-pair-01')/side/'lib';window=DIV/side/'lib'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded exits')
        need(sha(src)==sha(PKG/'CompactDecoderIff.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and row['stdout']==log.read_text(),'logs')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        parentfiles={p.relative_to(parent) for p in parent.rglob('*.olean')};windowfiles={p.relative_to(window) for p in window.rglob('*.olean')};files={p.relative_to(lib) for p in lib.rglob('*.olean')}
        extra={Path('DiophantineConsistency')/(x+'.olean') for x in ('CompactSelectorDiv','CompactCopy','CompactSelectorSum')};seeds={Path('DiophantineConsistency')/(x[1]+'.olean') for x in PARENTS}
        need(parentfiles==windowfiles|extra and files==parentfiles|seeds and not(parentfiles&seeds),'overlay membership')
        for rel in parentfiles:need((lib/rel).resolve()==(parent/rel).resolve() and sha(lib/rel)==sha(parent/rel),'parent overlay '+str(rel))
        for rel in windowfiles:need(sha(parent/rel)==sha(window/rel),'window '+str(rel))
        need(sha(window/'DiophantineConsistency/CompactSelector.olean')=='da6845b6426d5f6673facc34f7a2b840cd174202360dc2df67984ba84a6442f9','selector seed')
        for tag,module,prun,receipt,h in PARENTS:
            seed=lib/'DiophantineConsistency'/(module+'.olean');need(sha(seed)==sha(Path('/tmp')/prun/side/(module+'.olean'))==row['seed_sha256'][module]==h,'seed '+module)
        deps={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(x[1]+'.olean')) for x in PARENTS}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct dependencies')
        need(row['stdout']=="'CompactDecoderIff.decode_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and row['axiom_reports']==['propext, Classical.choice, Quot.sound'],'report')
        summaries.append({'side':side,'object_sha256':OBJECT,'parent_overlay_objects':len(parentfiles),'added_parent_seeds':2,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_DECODER_IFF_AUDIT','source_commit':'842f77f47a','author_receipt_sha256':RECEIPT,'recorded_outer_session':22578,'recorded_outer_exit':0,'parent_audit_rerun_exits':[0,0],'runs':summaries,'scope':'Conditional model finite-index decoder equivalence; assumptions are explicit, not obtained from graph. No 943-tile binding, checker calibration, iPRA proof or complete provider axiom inventory.'},indent=2))
if __name__=='__main__':main()
