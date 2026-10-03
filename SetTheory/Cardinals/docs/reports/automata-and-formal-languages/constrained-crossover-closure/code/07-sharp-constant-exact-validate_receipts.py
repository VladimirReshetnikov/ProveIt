import pathlib,json
R=pathlib.Path(__file__).resolve().parent
read=lambda n:json.loads((R/n).read_text())
two={'0':128,'1':1612,'2':188,'infinite':376}
three={'0':270336,'1':8680660,'2':2239104,'3':111984,'4':2016,'5':72,'infinite':1540884}
for name,counts,total,maxrank in [('two',two,2304,2),('three',three,12845056,5)]:
    r=read(f'independent_{name}_state.json')
    assert r['counts']==counts and r['total_directly_enumerated']==total
    assert r['maximum_finite_rank']==maxrank
    p=read(f'pointwise_{name}_state.json')
    assert p['passed'] and p['pointwise_three_algorithm_comparisons']==total
for name in ['original_cutoff_rerun.json','original_graph_rerun.json']:
    assert read(name)['counts']==three
lit=read('literal_receipt.json')
assert lit['passed'] and lit['two_state']['automata']==2304
assert lit['rank_five_automata']['automata']==72
assert len(lit['maximizer_classes'])==6
assert sum(c['size'] for c in lit['maximizer_classes'])==72
print('All audit receipts validated')
