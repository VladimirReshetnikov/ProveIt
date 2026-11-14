#!/usr/bin/env python3
"""Compare candidate against every complete corpus table using exact tuples."""
import argparse,hashlib,json
from pathlib import Path
from audit_corpus import parse,canonical,digest

def main():
 p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,required=True);p.add_argument('--native',type=Path);p.add_argument('--census-dir',type=Path,default=Path(__file__).parent);p.add_argument('--output',type=Path,required=True);p.add_argument('--expect-match',action='store_true');a=p.parse_args()
 data=a.candidate.read_bytes();rows,qs,start,hs=parse(data)
 assert len(hs)==1
 roots=[q for q in qs if canonical(rows,qs,q)[1]==len(qs)]
 assert roots
 forms={f'mirror={m},swap={s}':min(canonical(rows,qs,q,m,s)[0] for q in roots) for m in (False,True) for s in (False,True)}
 corpus=json.loads((a.census_dir/'class_canonical.json').read_text())
 relevant={h:tuple(tuple(t) for t in ts) for h,ts in corpus.items() if len(ts)==len(rows)}
 matches=[{'transformation':form,'corpus_table_class':h} for form,t in forms.items() for h,c in relevant.items() if t==c]
 out={'candidate':str(a.candidate),'sha256':hashlib.sha256(data).hexdigest(),'states':len(qs),'rows':len(rows),'declared_or_dense_start':start,'halt_labels':sorted(hs),'spanning_roots':len(roots),'graph_reachable_from_start':canonical(rows,qs,start)[1] if start is not None else None,'rooted_graph_sha256':digest(canonical(rows,qs,start)[0]) if start is not None else None,'table_class':digest(forms['mirror=False,swap=False']),'corpus_classes_total':len(corpus),'corpus_classes_same_size':len(relevant),'exact_tuple_comparisons':len(forms)*len(relevant),'matches':matches,'novel_under_state_renaming_any_spanning_root_reflection_bit_exchange':not matches,'method':'Equality of complete ordered transition tuples, not equality of hash digests. All choices of spanning root and four reflection/bit-exchange transformations are considered.'}
 if a.native:
  nd=a.native.read_bytes();nr,nq,ns,nh=parse(nd)
  if ns is None and 74 in nq: ns=74
  assert ns is not None and start is not None
  out['native_sha256']=hashlib.sha256(nd).hexdigest();out['native_start']=ns
  out['native_dense_exact_conjugacy']=canonical(rows,qs,start)[0]==canonical(nr,nq,ns)[0]
  assert out['native_dense_exact_conjugacy']
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
 assert bool(matches)==a.expect_match, 'novelty outcome does not match expectation'
if __name__=='__main__':main()
