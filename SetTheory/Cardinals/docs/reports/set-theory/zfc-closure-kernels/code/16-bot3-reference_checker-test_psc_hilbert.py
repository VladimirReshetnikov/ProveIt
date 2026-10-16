"""Semantic, proof-construction, binding, and rejection tests."""

import itertools
import json
import unittest

from psc_hilbert import (
    All, And, BOTTOM, CertificateError, Exists, Formula, Imp, Not, Or,
    Rel, Subset, Var, check_bytes, check_certificate, encode_formula,
    free_variables, length_lex_bytes, psc_instance, refutes_bytes,
    substitute, substitute_many, variable_names,
)


X, Y, Z, P = (Var(name) for name in ("x", "y", "z", "p"))


def identity_certificate(a):
    """The ordinary five-line K/S derivation, using constructed conclusions."""
    aa = Imp(a, a)
    return [
        {"op": "K", "A": encode_formula(a), "B": encode_formula(aa)},
        {"op": "K", "A": encode_formula(a), "B": encode_formula(a)},
        {"op": "S", "A": encode_formula(a), "B": encode_formula(aa),
         "C": encode_formula(a)},
        {"op": "MP", "premise": 0, "implication": 2},
        {"op": "MP", "premise": 1, "implication": 3},
    ]


def evaluate(formula, valuation, relation, domain=(0, 1)):
    """Independent direct semantics for the small formulae used in tests."""
    tokens = formula.tokens

    def read(position, environment):
        tag = tokens[position]
        if tag == "B":
            return False, position + 1
        if tag == "R":
            pair = (environment[tokens[position + 1]],
                    environment[tokens[position + 2]])
            return pair in relation, position + 3
        if tag == "I":
            left, middle = read(position + 1, environment)
            right, end = read(middle, environment)
            return (not left or right), end
        name = tokens[position + 1]
        values = []
        for value in domain:
            local = dict(environment)
            local[name] = value
            truth, end = read(position + 2, local)
            values.append(truth)
        return all(values), end

    truth, end = read(0, valuation)
    assert end == len(tokens)
    return truth


class FormulaTests(unittest.TestCase):
    def test_primitive_bottom_and_flat_grammar(self):
        self.assertNotEqual(BOTTOM, Rel(X, X))
        self.assertEqual(Formula(("B",)), BOTTOM)
        for malformed in ((), ("R", "x"), ("B", "B"), ("I", "B"),
                          ("A", "x"), ("E", "x", "y"), ("R", "x", True)):
            with self.subTest(malformed=malformed), self.assertRaises(CertificateError):
                Formula(malformed)

    def test_deep_formula_does_not_use_python_recursion(self):
        formula = Formula(("A", "z") * 2500 + ("R", "x", "z"))
        self.assertEqual(free_variables(formula), {"x"})
        result = substitute(formula, X, Y)
        self.assertEqual(result.tokens[-3:], ("R", "y", "z"))
        self.assertEqual(free_variables(result), {"y"})

    def test_same_variable_and_nonfree_substitution(self):
        formula = Imp(Rel(X, Y), All(X, Rel(X, Y)))
        self.assertEqual(substitute(formula, X, X), formula)
        self.assertEqual(substitute(All(X, Rel(X, Y)), X, Y), All(X, Rel(X, Y)))

    def test_capture_avoidance_and_shadowing(self):
        formula = All(Y, Imp(Rel(X, Y), All(Y, Rel(X, Y))))
        result = substitute(formula, X, Y)
        v0, v1 = Var("_v0"), Var("_v1")
        expected = All(v0, Imp(Rel(Y, v0), All(v1, Rel(Y, v1))))
        self.assertEqual(result, expected)
        self.assertEqual(free_variables(result), {"y"})

    def test_renaming_avoids_existing_bound_and_free_names(self):
        formula = All(Y, And(Rel(X, Y), All(Var("_v0"), Rel(P, Var("_v0")))))
        result = substitute(formula, X, Y)
        expected = All(Var("_v1"), And(Rel(Y, Var("_v1")),
                       All(Var("_v0"), Rel(P, Var("_v0")))))
        self.assertEqual(result, expected)

    def test_simultaneous_substitution_is_not_sequential(self):
        self.assertEqual(substitute_many(Rel(X, Y), {"x": "y", "y": "x"}),
                         Rel(Y, X))
        with self.assertRaises(CertificateError):
            substitute_many(Rel(X, Y), {True: True})

    def test_substitution_semantic_lemma(self):
        formulae = [Rel(X, Y), All(Y, Rel(X, Y)),
                    All(Y, Imp(Rel(X, Y), All(X, Rel(X, Y))))]
        pairs = list(itertools.product((0, 1), repeat=2))
        for formula in formulae:
            replaced = substitute(formula, X, Y)
            for mask in range(16):
                relation = {pair for i, pair in enumerate(pairs) if mask & (1 << i)}
                for vx, vy in itertools.product((0, 1), repeat=2):
                    assignment = {"x": vx, "y": vy}
                    changed = dict(assignment, x=vy)
                    self.assertEqual(evaluate(replaced, assignment, relation),
                                     evaluate(formula, changed, relation))


class CalculusTests(unittest.TestCase):
    def test_valid_identity_and_theorem_generalization(self):
        a = Rel(X, Y)
        certificate = identity_certificate(a)
        proof = check_certificate(certificate)
        self.assertEqual(proof.conclusion, Imp(a, a))
        self.assertFalse(proof.is_refutation)
        certificate.append({"op": "GEN", "line": 4, "x": "x"})
        self.assertEqual(check_certificate(certificate).conclusion, All(X, Imp(a, a)))

    def test_propositional_basis_has_classical_semantics(self):
        a, b, c = Rel(X, X), Rel(X, Y), Rel(Y, X)
        certificate = [
            {"op": "K", "A": encode_formula(a), "B": encode_formula(b)},
            {"op": "S", "A": encode_formula(a), "B": encode_formula(b),
             "C": encode_formula(c)},
            {"op": "C", "A": encode_formula(a), "B": encode_formula(b)},
        ]
        lines = check_certificate(certificate).lines
        pairs = list(itertools.product((0, 1), repeat=2))
        for mask in range(16):
            relation = {pair for i, pair in enumerate(pairs) if mask & (1 << i)}
            for formula in lines:
                self.assertTrue(evaluate(formula, {"x": 0, "y": 1}, relation))

    def test_primitive_bottom_has_a_derived_explosion_law(self):
        # This fails for an implicational basis that treats BOTTOM as a
        # free propositional atom.  The classical C schema is essential.
        a = Rel(X, Y)
        certificate = identity_certificate(BOTTOM)  # line 4: not Bottom
        certificate.extend([
            {"op": "K", "A": encode_formula(Not(BOTTOM)),
             "B": encode_formula(Not(a))},
            {"op": "MP", "premise": 4, "implication": 5},
            {"op": "C", "A": encode_formula(a), "B": encode_formula(BOTTOM)},
            {"op": "MP", "premise": 6, "implication": 7},
        ])
        proof = check_certificate(certificate)
        self.assertEqual(proof.conclusion, Imp(BOTTOM, a))
        self.assertFalse(proof.is_refutation)

    def test_ui_same_variable_and_cross_variable(self):
        a = Rel(X, Y)
        same = [{"op": "UI", "x": "x", "A": encode_formula(a), "y": "x"}]
        self.assertEqual(check_certificate(same).conclusion, Imp(All(X, a), a))
        body = All(Y, Rel(X, Y))
        other = [{"op": "UI", "x": "x", "A": encode_formula(body), "y": "y"}]
        renamed = All(Var("_v0"), Rel(Y, Var("_v0")))
        result = check_certificate(other).conclusion
        self.assertEqual(result, Imp(All(X, body), renamed))
        for relation in (set(), {(0, 0)}, {(0, 1), (1, 0)},
                         set(itertools.product((0, 1), repeat=2))):
            for vx, vy in itertools.product((0, 1), repeat=2):
                self.assertTrue(evaluate(result, {"x": vx, "y": vy}, relation))

    def test_quantifier_distribution_and_its_side_condition(self):
        a, b = Rel(Y, Y), Rel(X, Y)
        certificate = [{"op": "QD", "x": "x", "A": encode_formula(a),
                        "B": encode_formula(b)}]
        self.assertEqual(check_certificate(certificate).conclusion,
                         Imp(All(X, Imp(a, b)), Imp(a, All(X, b))))
        certificate[0]["A"] = encode_formula(Rel(X, Y))
        with self.assertRaisesRegex(CertificateError, "not free"):
            check_certificate(certificate)

    def test_reference_validation_including_python_booleans(self):
        prefix = identity_certificate(Rel(X, Y))
        for invalid in (-1, 5, True, False, 0.0, "0", None):
            with self.subTest(reference=invalid), self.assertRaises(CertificateError):
                check_certificate(prefix + [{"op": "GEN", "line": invalid, "x": "x"}])
        with self.assertRaises(CertificateError):
            check_certificate(prefix + [{"op": "MP", "premise": 0, "implication": 1}])
        with self.assertRaises(CertificateError):
            check_certificate([{"op": "MP", "premise": 0, "implication": 0}])

    def test_no_assertions_and_no_unchecked_extra_fields(self):
        for op in ("ASSERT", "ASSUME", "axiom", "IR", "EXT", "", False):
            with self.subTest(op=op), self.assertRaises(CertificateError):
                check_certificate([{"op": op, "A": ["B"]}])
        with self.assertRaises(CertificateError):
            check_certificate([{"op": "K", "A": ["B"], "B": ["B"],
                                "conclusion": ["B"]}])

    def test_only_primitive_bottom_is_a_refutation(self):
        self.assertFalse(check_certificate([]).is_refutation)
        self.assertFalse(check_certificate(identity_certificate(BOTTOM)).is_refutation)
        self.assertFalse(check_certificate(identity_certificate(Rel(X, X))).is_refutation)


class PSCTests(unittest.TestCase):
    def test_exact_schema_with_fresh_binders_and_global_support(self):
        # Parameter p is closed; a matrix binder called a is preserved.
        a = Var("a")
        matrix = Imp(Rel(X, P), All(a, Rel(Y, a)))
        v = [Var(f"_v{i}") for i in range(11)]

        def rho(first, second):
            return Imp(Rel(first, P), All(a, Rel(second, a)))

        # Independently spell out the schema, especially unrestricted support.
        expected_bound = All(v[0], Exists(v[1], All(v[2], Imp(
            rho(v[0], v[2]), All(v[3], Imp(Rel(v[3], v[2]), Rel(v[3], v[1])))))))
        expected_closure = All(v[6], All(v[7], Imp(And(
            Or(All(v[8], Imp(Rel(v[8], v[6]), Rel(v[8], v[4]))),
               Rel(v[6], v[5])), rho(v[6], v[7])), Rel(v[7], v[5]))))
        expected_support = All(v[9], Imp(Rel(v[9], v[5]),
                                       Exists(v[10], rho(v[10], v[9]))))
        expected = All(P, Imp(expected_bound, All(v[4], Exists(v[5],
                                 And(expected_closure, expected_support)))))
        result = psc_instance(matrix, X, Y)
        self.assertEqual(result, expected)
        self.assertEqual(free_variables(result), set())
        row = {"op": "PSC", "rho": encode_formula(matrix), "x": "x", "y": "y"}
        self.assertEqual(check_certificate([row]).conclusion, expected)

    def test_bound_slots_and_reserved_fresh_names_are_preserved(self):
        matrix = And(Rel(X, Y), All(X, Rel(X, Var("_v0"))))
        result = psc_instance(matrix, X, Y)
        self.assertEqual(result.tokens[:2], ("A", "_v0"))  # free parameter closure
        self.assertEqual(free_variables(result), set())
        self.assertIn("_v11", variable_names(result))
        # Three rho copies preserve their original bound x; no free x remains.
        self.assertEqual(sum(result.tokens[i:i+2] == ("A", "x")
                             for i in range(len(result.tokens)-1)), 3)

    def test_arbitrary_matrix_complexity_and_absent_slots(self):
        for matrix in (BOTTOM, Not(Rel(X, Y)), All(X, Not(All(Y, Rel(X, Y))))):
            result = psc_instance(matrix, X, Y)
            self.assertEqual(free_variables(result), set())
        with self.assertRaises(CertificateError):
            psc_instance(Rel(X, Y), X, X)
        with self.assertRaises(CertificateError):
            check_certificate([{"op": "PSC", "rho": ["E", "x", "y"],
                                "x": "x", "y": "y"}])


class SerializationTests(unittest.TestCase):
    def test_json_roundtrip_and_total_rejections(self):
        certificate = identity_certificate(Rel(X, Y))
        encoded = json.dumps(certificate).encode("utf-8")
        self.assertEqual(check_bytes(encoded), check_certificate(certificate))
        for invalid in (b"", b"\xff", b"{}", b"null", b"[true]",
                        b'[{"op":"GEN","line":true,"x":"x"}]',
                        b'[{"op":"GEN","line":NaN,"x":"x"}]',
                        b'[{"op":"K","op":"ASSERT","A":["B"],"B":["B"]}]',
                        b"[" * 3000 + b"]" * 3000):
            with self.subTest(invalid=invalid[:50]):
                self.assertFalse(refutes_bytes(invalid))

    def test_byte_enumeration_length_then_lexicographic(self):
        stream = length_lex_bytes()
        prefix = list(itertools.islice(stream, 258))
        self.assertEqual(prefix[0], b"")
        self.assertEqual(prefix[1:257], [bytes([i]) for i in range(256)])
        self.assertEqual(prefix[257], b"\x00\x00")


if __name__ == "__main__":
    unittest.main()
