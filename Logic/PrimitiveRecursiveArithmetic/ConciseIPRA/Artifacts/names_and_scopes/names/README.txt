K1: EQUATIONAL ALIASES WITH ONE NAMING SCHEMA

This directory contains a readable standalone proof checker, an untrusted
proof compiler, portable source fixtures, and generated certificates.

The mathematical contribution is a restricted proof interface and its exact
boundary. Alias and backward substitution conclude literal equations only.
Specialization and introduction select the newest parameter (zero in an
empty scope). The only additional compound primitive is

    Name(t) = D_{x,y}(I(y,t;u.x)=t).

It is equivalent to permitting precisely the compound Alias export
Name(b) -> Name(t) under a fresh b=t. Names recover full formula transport,
arbitrary specialization, arbitrary introduction witnesses, and full Alias
through the simultaneous rank induction described in the accompanying paper.
Without this naming capability, the growing-domain evaluation separates
the ordinary theorem Name(1).

This is not a new compact checker-size record. The complete checker is
readable reference code; its source and all validation costs are included.

RUNNING

From this directory:

    python3 names_kernel.py < tests/name_one.json
    python3 compile_names.py < reference/source_fixtures/transport_beneath_D.json
    python3 verify_names.py

The checker prints ACCEPT and exits zero on acceptance; it prints REJECT
and exits one after any validation or execution error. It uses json and
sys from the Python standard library only. The compiler and verification
script are untrusted: every compiled closed certificate is rechecked by
the standalone kernel, also in isolated Python with optimization enabled.

INPUT SYNTAX

Terms in scope n, with local binder depth d:

    0         zero
    -1..-n    free parameters; -n is newest
    1..d      local bound indices, nearest first
    [0,t]     successor
    [n,a,h]   I(n,a;u.h); u is index 1 inside h

Formulas:

    [s,t]     equation
    [B]       D_{x,y} B; x is index 2, y index 1

The raw syntax performs no normalization. For an externally scoped term t,
Name(t) has JSON representation [[[1,t,3],t]]: the index for x is 3 inside
the iterator body, after its additional u binder. Since t has no free
positive indices at its input boundary, it needs no lifting when inserted.

A context entry (base,body) represents base -> forall y body. base=[]
means no antecedent. An assumption A is ([],A) with unused clause binder.
Contexts and scopes are empty at the standalone entry point; open-sequent
contexts are only an in-process API used by the compiler and tests.

PROOF NODES

    ["n",t]
      Derive Name(t). Validate t over the current numerical scope.

    ["u",index,premise]
      Use the indexed context clause at the newest parameter, or zero.
      Check its antecedent with premise if it has one. An unused premise
      payload is ignored, matching the inherited rule-directed contract.

    ["c",counter,seed,body]
      Derive the computation equation at counter 0 or literal [0,n].
      The entire term, including an unused body, is validated.

    ["v",goal,major,minor]
      goal is an equation. major proves b=t for newest b; minor proves
      goal[t/b]. Conclude goal. The replacement t may contain b.

    ["a",target,branch]
      Introduce fresh b and assumption b=target. The branch result E must
      be an equation. Conclude E[target/b]. target is validated in the
      outer scope, so it cannot contain b.

    ["e",goal,major,branch]
      major proves D B. Introduce fresh b and the clause
      [B(b,0);y.B(b,y)]. The branch proves goal. goal is validated over
      the outer scope and therefore cannot contain b.

    ["i",goal,branch]
      goal is D B. Select newest witness w (zero if the scope is empty).
      Introduce fresh z. Assume B(w,z) if raw B is diagonal, and B(w,0)
      otherwise. Check that the branch proves B(w,Sz).

The diagonal selector recognizes an equation with both sides iterators
whose counter and seed are the bound y: both prefixes are literally [1,1].
It is applied before witness substitution.

The closed input envelope has exactly keys goal and proof:

    {"goal": <closed formula>, "proof": <proof node>}

SOURCE CALCULUS

source_liberal.py is the inherited reference calculus. Its Use supplies an
arbitrary term, Close supplies an arbitrary witness, Back allows any formula
and any current parameter, and Alias allows any formula. compile_names.py
compiles this calculus to K1 without emitting any compound Alias.

EVIDENCE

verify_names.py checks 19 inherited closed source fixtures, two extra closed
translations (Name(1) and compound Alias), the direct Name(1) certificate,
and 13 open translations. The open cases include ranks 1 through 3, both
introduction modes, self-containing replacements, and a non-order-preserving
scope injection with noncontiguous context positions. It runs 60 standalone
normal/optimized checks, including eight malformed/forbidden examples.

evidence/verification.json records the results and exact metric convention.
These are finite implementation checks, not a Lean/Rocq formalization or
an exhaustive theorem about all runtime inputs. The mathematical proof is
separate; no consistency claim is inferred from testing alone.

PROVENANCE

Derived from the equational_transport incoming package in ProveIt snapshot
fc05b10f0e03f22edbfdde9298a29fb2fee5dc59. See PROVENANCE.json and LICENSE.txt.
The inherited rank-induction architecture is credited in the paper; the
new work is the joint-restriction separation and its naming-only repair.
