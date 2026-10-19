"""Check frozen premises of the routing183 conditional six-zero lower bound.

The general tree argument is stated in grammar_research_notes.tex. This script
checks its finite source and caller premises; it is not a proof-assistant proof.
"""
import os,json,pathlib,hashlib
HERE=pathlib.Path(__file__).resolve().parent
BASE=pathlib.Path(os.environ.get('ZFC245_BASE',str(HERE.parent/'baseline245/zfc245-proof-20261018')))
source_path=BASE/'reference/grammar/closed-sequence-grammar-next22.json'
s=json.loads(source_path.read_text());sym=json.loads((BASE/'reference/grammar/semantic-symbols.json').read_text());enc={v:k for k,v in sym.items()}
names={int(q):''.join(enc[a] for a in word) for q,word in s['flattened_semantic_words'].items()}
by_ast={int(v):int(q) for q,v in s['sequence_ast_roots'].items()};dag=s['ast_dag']
C='VqkjGqkjGVqkjG';B='qkjG';E='VqkjG'
assert names[213]==C and names[23]=='eijk'
assert s['atoms'][sym['P']]['ast']==173 and dag[173]==['N',153,120] and by_ast[153]==213
assert s['atoms'][sym['V']]['ast']==112 and dag[112]==['N',57,42] and by_ast[57]==23
assert s['atoms'][sym['e']]['ast']==40 and dag[40]==['N',39,21] and dag[39]==['L',['dec',1]]
assert all(i not in by_ast for i in [173,112,40])
cs=[c for c in s['left_entry_projection_constraints'] if c['reason']['source']==183 and c['reason']['read']==1]
assert {(x['prefix'],''.join(enc[a] for a in x['word'])) for x in cs}=={('01',B),('11',E)}
assert names[76].count('P')==1
sample=json.loads((HERE/'zero5-feasibility-best.json').read_text())
assert next(x['word'] for x in sample['routes'] if(x['source'],x['read'])==(183,1))==C
result={
 'status':'FINITE_PREMISES_PASS',
 'source_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
 'conditional_statement':'In an orientation-valid semantic-word grammar retaining the original AX spelling and routing183/1 to C, the expanded source has maximum zero run at least6, independent of the number of grammar states.',
 'C':C,'caller':{'source':183,'read':1,'requirements':[['01',B],['11',E]]},
 'fixed_nodes':{'P':['N','C','eijkKCeijkfgW'],'V':['N','eijk','l'],'e':['N',['dec',1],'remaining_e_body']},
 'leading_zero_lower_bounds':{'e':1,'eijk':2,'V':3,'nonempty_prefix_starting_V':3,'C_given_projection01':5,'P':6},
 'original_AX_P_occurrences':1,
 'minimal_escape_conditions':['Route183/1 to a different word/state so the source C parse is free.','Change the AX spelling to remove the fixed P occurrence, then analyze other forced source prefixes.','Generalize the compiler to permit distinct state roles with the same semantic word and different parsing trees.'],
 'scope':'A human proof using these checked finite premises is supplied in grammar_research_notes.tex; no unconditional state lower bound or new kernel theorem is claimed.'
}
(HERE/'routing183-obstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
