from pathlib import Path
import sys,json
sys.dont_write_bytecode=True;sys.path.insert(0,'analysis/comparison');import source_inventory as I
L=I.L;src=I.base/'machine/variant_plain/u208.sites.json';rs=json.loads(src.read_text());root=L.tree(rs)
p='001101110';node=L.subtree(root,p);assert len(L.sites(node))==19 and L.boundary(node)==(0,0,False)
parent=p[:-1];side=int(p[-1]);sibling=L.subtree(root,parent)[1-side];assert L.boundary(sibling)==(0,0,False)
new=L.replace(root,parent,sibling);nr=L.sites(new);g=L.graph_arithmetic(rs)[0];ng=L.graph_arithmetic(nr)[0]
lo,hi=3847,3866
assert[(o,a)for _,o,a in nr]==[(o,a)for i,(_,o,a)in enumerate(rs)if not lo<=i<hi]
def idx(i):
 if lo<=i<hi:i=hi
 return i if i<lo else i-(hi-lo)
expected=[[eff,[idx(z)for z in zs]]for i,(eff,zs)in enumerate(g)if not lo<=i<hi]
assert ng==expected
assert g==L.graph_intervals(rs) and ng==L.graph_intervals(nr)
out=Path('analysis/reduction_search/no_mp_padding');out.mkdir(exist_ok=True)
(out/'source.sites.json').write_text(json.dumps(nr,separators=(',',':'))+'\n')
(out/'source.sites.tsv').write_text(''.join(f'{p}\t{o}\t{a if a is not None else -1}\n'for p,o,a in nr))
(out/'old_padding_macro.json').write_text(json.dumps(L.sites(node),indent=2)+'\n')
report={'old_metrics':L.metrics(root),'new_metrics':L.metrics(new),'removed_interval':[lo,hi],'removed_prefix':p,'parent_prefix':parent,'sibling_boundary':L.boundary(sibling),'cfg_skip_check':True,'startup_source_ordinal136_preserved':nr[136]==rs[136],'old_block_effect':'(T,W) -> (0,P(T,W)); scratches zero','entry_T_is_zero':True,'new_MP_success':'(z,w,z,0)','old_MP_success':'(z,P(0,w),z,0)'}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
