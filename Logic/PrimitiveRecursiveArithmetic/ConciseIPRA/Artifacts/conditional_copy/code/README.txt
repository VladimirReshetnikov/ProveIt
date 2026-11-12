CHECKER INTERFACE
=================

checker.py is the complete selected acceptance module. It imports only json.
Run:
  python3 code/checker.py < validation/fixtures/positive/reflexivity.json
Acceptance means exit status zero and exactly ACCEPT followed by a newline.
The other scripts in code/ are controls or untrusted proof producers.

The input is [goal, proof]. Numerical zero is the integer 0, negative integers
are free numerical parameters, and positive integers are de Bruijn bound
indices. At the root no free parameter is available. A term is an integer or
[counter, seed, body], representing R(counter,seed;i,u.body), with u at bound
index 1 and i at index 2. Successor is [0,term,0]. Numerical terms must already
be full computation normal forms. A formula is [left,right] for equality or
[matrix] for D_x,y matrix, with y at bound index 1 and x at index 2.

The initial context contains the single unconditional clause with body [1,1],
i.e. universal reflexivity. A retained clause is internally (base,body), where
[] denotes no antecedent and body has one implicit specialization variable.
Every introduction/export extends the context by one clause and allocates one
fresh negative parameter. If n is the context length, the new parameter is -n;
the newest outer parameter is 1-n, which is zero at the root.

There are exactly three certificate patterns:

  [j, t, p]             Use clause j at t. If the clause has an antecedent,
                        p must prove it. An unused p is conventionally null.
  [B, p]                Introduce D B, with B a nonempty matrix tree.
                        The witness is fixed by the current scope. The
                        normalized zero row 0=0 selects progress; every
                        other zero row selects the case premise.
  [[], p, q]            Export. p proves a D formula. q runs in its opened
                        clause. If its zero row is literally 0=0 and its
                        first positive row is b=t, t is substituted for b
                        in the result of q; otherwise no substitution is
                        made. The exported result must be well scoped in
                        the outer context.

Every inferred conclusion is checked for sort, scope and canonical form.
The final asserted goal is compared type-exactly by repr to the validated
inferred formula. This rejects Boolean and float aliases of integer leaves.
Scope/sort validation traverses children before any computation can erase
an unused zero-counter body.

checker_fuel.py takes [goal,proof,fuel], where fuel is a nonnegative integer.
It spends one unit at entry to every syntax traversal and proof call.
A successful run has exactly the same accepted goal/proof as checker.py.
A larger sufficient budget changes no rule or theorem.

MATCHED CONTROLS
---------------
control_witness.py differs at introduction only:
  [B,t,p]               Supply the witness t explicitly.

control_name.py differs at export only:
  [[],p,e,q]            In the opened context e must prove b=t. Then export
                        the result of q after substituting t for b.

Their _fuel.py counterparts apply the same budget instrumentation.
The explicit Name program is a few bytes smaller than inferred Export;
its certificate interface has an additional equality-proof input.

UNTRUSTED SUPPORT
-----------------
proof_tools.py builds examples from the written constructions.
translate_witness.py implements the relative proof translation from the
supplied-witness control, rebuilding assumptions in their actual scopes.
Neither is imported by the checker. The validation scripts replay every
produced certificate through the complete standalone checker.

BACKWARD NAME VARIANT
---------------------
checker_backward_name.py is an alternative complete standalone checker.
It has the same numerical syntax, fixed reflexivity clause, and deterministic
introduction selector. Its input is [goal,proof], but its proof interface is
backward and explicitly tagged:

  ['u',j,t,p]                         Use clause j at t.
  ['i',branch]                        Introduce the supplied D goal.
  ['e',B,T,t,major,equality,branch]    Open D B at fresh b; prove b=t and
                                      NF(T[b/v]); require NF(T[t/v]) to
                                      be the supplied outer goal.

Here T has one implicit template slot v, represented by one additional bound
index. Both normalized endpoint formulas are independently checked. The
written representation lemma proves that this is exactly Name, even when T
explicitly mentions b and t itself contains b. Its proof uses preservation of
normal forms under arbitrary parameter renaming, not just normalization
coherence. Unallocated auxiliary parameters may be erased at both endpoints;
the inherited template-completion lemma supplies a well-scoped replacement.
Active formulas, the equality target and both endpoints remain validated.

This variant retains a replacement term, an equality proof and a template at
discharge. It is distinct from the automatic Export interface. It has 1907
normalized bytes, 619 significant tokens and 686 AST nodes under CPython
3.12.14, versus 1925/630/701 for the included parameter_intro reference.
The supplied source equation field of that reference is fixed to b, and its
reflexive-base selector is replaced by the exact 0=0 selector.
