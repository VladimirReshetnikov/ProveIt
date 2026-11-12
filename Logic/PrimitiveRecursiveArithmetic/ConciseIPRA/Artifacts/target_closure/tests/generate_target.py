"""Untrusted named-syntax producer for the target-directed calculus.

It reuses the attributed named-term encoder and elementary equality proof
macros. It does not import a checker or a checker substitution function.
"""
import copy
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'reference'))
import named_producer as g

def closure(env=()):
    return g.elim(g.Q('index',g.identity('index')),g.progressive_pair(env),['hyp',0],env)

def use(target,major,minor,env=()):
    return ['use',g.te(target,env),major,minor]

def identity_base(env=()):
    return g.zero(0,'identity_state',g.S('identity_state'),env)

def anchored_identity(target,env=()):
    box=g.I(0,target,'box_state',0)
    at_box=use(box,closure(env),identity_base(env),env)
    return g.tr('box_value',g.identity('box_value'),g.zero(target,'box_state',0,env),at_box,env)

def build():
    folder=ROOT/'tests/target'
    folder.mkdir(exist_ok=True)
    cases=[]
    def add(name,data,accept,note=''):
        (folder/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        cases.append(dict(file=name+'.json',accept=accept,note=note))
    def put(name,goal,proof,accept=True,note=''):
        add(name,g.package(goal,proof),accept,note)
    one,two,three=g.S(0),g.S(g.S(0)),g.S(g.S(g.S(0)))
    put('zero_computation',g.Eq(g.I(0,one,'u',0),one),g.zero(one,'u',0))
    put('successor_computation',g.Eq(g.I(one,one,'u',g.S('u')),g.S(g.I(0,one,'u',g.S('u')))),g.succ(0,one,'u',g.S('u')))
    put('derived_reflexivity',g.Eq(two,two),g.refl(two))
    put('atomic_intro_used_induction_hypothesis',g.D('unused_witness','index',g.identity('index')),g.progressive_pair(),note='The equation-induction premise actually uses its local equation through transport.')
    put('closure_extraction',g.Q('index',g.identity('index')),closure())
    box=g.I(0,three,'box_state',0)
    put('nonsuccessor_target_base_branch',g.identity(box),use(box,closure(),identity_base()),note='The target is iterator-headed, so the minor must be E(0).')
    put('zero_target_base_branch',g.identity(0),use(0,closure(),identity_base()))
    put('anchored_closure_at_successor',g.identity(three),anchored_identity(three),note='Uses an iterator-headed box followed by equational transport to recover arbitrary anchored closure.')
    put('successor_target_progress_branch',g.identity(three),use(three,closure(),anchored_identity(two)),note='The syntactic target S(2) requires E(2), then gives E(3).')

    stable=g.D('inner_x','inner_y',g.Eq(0,0))
    stable_proof=g.intro('inner_x','inner_y',g.Eq(0,0),0,g.refl(0,('z',)))
    compound=g.D('outer_x','outer_y',stable)
    compound_proof=g.intro('outer_x','outer_y',stable,0,['hyp',0])
    compound_closure=g.elim(g.Q('outer_y',stable),compound_proof,['hyp',0])
    put('compound_case_intro',compound,compound_proof)
    put('compound_successor_target_uses_base',stable,use(three,compound_closure,stable_proof),note='Even at a successor target, a compound matrix uses its zero instance.')

    put('wrong_progress_antecedent',g.identity(three),use(three,closure(),identity_base()),False,'E(0) cannot directly discharge the E(2) premise selected by target S(2).')
    put('wrong_base_antecedent',g.identity(box),use(box,closure(),anchored_identity(one)),False,'An iterator-headed target selects E(0), not E(1).')
    put('false_equality',g.Eq(0,one),g.refl(0),False)
    put('wrong_computation_endpoint',g.Eq(g.I(0,one,'u',0),0),g.zero(one,'u',0),False)

    bad=copy.deepcopy(g.progressive_pair());bad[2]=['v',0]
    put('future_di_witness',g.D('unused_witness','index',g.identity('index')),bad,False)
    bad=['elim',['=', ['v',0],['v',0]],g.progressive_pair(),['hyp',0]]
    add('existential_eigenvariable_escape',{'goal':['=',0,0],'proof':bad},False,'DE conclusion cannot contain the fresh witness.')
    put('unbound_iterator_state',g.Eq(0,0),['zero',0,['v',1]],False)
    add('open_public_goal',{'goal':['=', ['v',0],0],'proof':g.refl(0)},False,'The standalone interface admits only closed goals.')
    for label,scalar in [('boolean',False),('float',0.0),('string','0')]:
        add('bad_'+label+'_term',{'goal':['=',scalar,0],'proof':g.refl(0)},False,'The public grammar uses exact integer zero, not coercible aliases.')
    add('malformed_proof',{'goal':['=',0,0],'proof':['zero',0]},False,'The computation packet is missing its bound body.')
    add('boolean_hypothesis_index',{'goal':['=',0,0],'proof':['hyp',False]},False)
    add('negative_hypothesis_index',{'goal':['=',0,0],'proof':['hyp',-1]},False)
    add('extra_public_field',{'goal':['=',0,0],'proof':g.refl(0),'extra':0},False)
    add('malformed_formula',{'goal':['q',['=',0,0],0],'proof':closure()},False)

    b=g.Q('dummy',g.Eq('outer',0))
    bad=g.intro('unused','outer',b,0,['hyp',0])
    put('compound_progress_not_allowed',g.D('unused','outer',b),bad,False,'A compound premise retains B(0), so a progressive hypothesis cannot be substituted for it.')
    ordinary=g.Eq('index',one)
    old_case=g.intro('unused','index',ordinary,0,g.explosion(g.S('z'),one,('z',)))
    put('old_atomic_case_not_allowed',g.D('unused','index',ordinary),old_case,False,'Atomic introduction is uniformly progressive in this calculus.')
    boxed=copy.deepcopy(old_case);boxed[2]=g.te(g.I(0,0,'box_state',0))
    put('boxed_witness_does_not_change_intro',g.D('unused','index',ordinary),boxed,False,'A nonliteral zero witness does not switch to atomic cases here.')

    # Open sequents exercise the meaning of atomic progress and the absence
    # of compound induction. They are not standalone closed certificates.
    parity_eq=lambda y:g.Eq(g.parity(y),one)
    progress_context=[g.fe(g.Q('index',parity_eq('index')))]
    e_two=use(two,['hyp',0],g.parity_one())
    contradiction=g.tr('parity_result',g.Eq('parity_result',one),g.parity_two(),e_two)
    compound_at=lambda y:g.D('cx','cy',g.Eq(g.I('cy',0,'cu',y),g.I('cy',0,'cv',one)))
    open_cases=[
        dict(name='atomic_progress_full_strength',scope=0,context=progress_context,goal=g.fe(g.Eq(0,one)),proof=contradiction,accept=True,note='OPEN sequent under a false progressive parity assumption; this is not a closed proof of contradiction.'),
        dict(name='compound_progress_rejected',scope=0,context=[g.fe(g.Q('index',compound_at('index'))),g.fe(compound_at(one))],goal=g.fe(compound_at(two)),proof=use(two,['hyp',0],['hyp',1]),accept=False,note='Both compound assumptions have a standard-number model, but the illicit progressive conclusion fails there.'),
        dict(name='variable_target_uses_base',scope=1,context=[g.fe(g.Q('index',g.identity('index')),('x',))],goal=g.fe(g.identity('x'),('x',)),proof=use('x',['hyp',0],identity_base(('x',)),('x',)),accept=True,note='A variable is syntactically a nonsuccessor target.'),
        dict(name='literal_substitution_needs_repair',scope=0,context=[g.fe(g.Q('index',g.identity('index')))],goal=g.fe(g.identity(three)),proof=use(three,['hyp',0],identity_base()),accept=False,note='Replacing the variable target by S(2) in the original proof packet changes its required minor premise.'),
        dict(name='substitution_repaired_by_boxing',scope=0,context=[],goal=g.fe(g.identity(three)),proof=anchored_identity(three),accept=True,note='The derived anchored rule repairs the substitution instance.'),
    ]
    (ROOT/'tests/target_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    (ROOT/'tests/target_open_cases.json').write_text(json.dumps(open_cases,indent=2)+'\n')
    return cases,open_cases

if __name__=='__main__':
    a,b=build();print(len(a),'closed cases;',len(b),'open cases')
