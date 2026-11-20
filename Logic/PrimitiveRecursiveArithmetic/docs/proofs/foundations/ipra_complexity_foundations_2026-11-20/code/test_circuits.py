"""Finite regression checks for the circuit/CNF reference implementation.

These tests compare independently written tape simulation and circuit
evaluation at every represented time and tape position. They do not replace
the report's general mathematical proofs or the Lean proof roadmap.
"""

from itertools import product
import unittest

from circuits import (
    ALPHABET, BLANK, Builder, Circuit, Gate, TapeMachine,
    cnf_value, compile_verifier, parity_machine, simulate_trace,
)


def bits(width):
    return product((False, True), repeat=width)


class TestTseitin(unittest.TestCase):
    def test_all_assignments_for_tiny_circuits(self):
        circuits = [
            Circuit(1, (), 0),
            Circuit(0, (Gate("const", value=False),), 0),
            Circuit(0, (Gate("const", value=True),), 0),
            Circuit(1, (Gate("not", (0,)),), 1),
            Circuit(2, (Gate("and", (0, 1)),), 2),
            Circuit(1, (Gate("and", (0, 0)),), 1),
            Circuit(2, (Gate("and", (0, 1)), Gate("not", (2,)),
                        Gate("const", value=True), Gate("and", (3, 4))), 5),
        ]
        assignment_checks = 0
        for circuit in circuits:
            constraints = circuit.tseitin(require_output=False)
            accepting_cnf = circuit.tseitin()
            self.assertLessEqual(len(accepting_cnf),
                                 3 * len(circuit.gates) + circuit.inputs + 1)
            self.assertTrue(all(1 <= len(c) <= 3 for c in accepting_cnf))
            for assignment in bits(circuit.wires):
                extension = circuit.extend(assignment[:circuit.inputs])
                self.assertEqual(cnf_value(constraints, assignment), assignment == extension)
                accepts = assignment == extension and assignment[circuit.output]
                self.assertEqual(cnf_value(accepting_cnf, assignment), accepts)
                if accepts:
                    witness = circuit.restrict(assignment)
                    self.assertEqual(witness, assignment[:circuit.inputs])
                    self.assertTrue(circuit.evaluate(witness))
                else:
                    with self.assertRaises(ValueError):
                        circuit.restrict(assignment)
                assignment_checks += 1
        self.assertEqual(assignment_checks, 86)

    def test_unused_inputs_survive_renaming_and_preserve_multiplicity(self):
        # The output ignores all three certificate bits. With a true output,
        # precisely eight certificates must remain after renaming variables
        # solely by their occurrence in the serialized CNF. Without input
        # tautologies that renaming would collapse the count to one.
        for value in (False, True):
            circuit = Circuit(3, (Gate("const", value=value),), 3)
            cnf = circuit.tseitin()
            occurring = sorted({abs(literal) for clause in cnf for literal in clause})
            self.assertEqual(occurring, [1, 2, 3, 4])
            renaming = {old: new + 1 for new, old in enumerate(occurring)}
            renamed = tuple(tuple(renaming[abs(lit)] if lit > 0
                                  else -renaming[abs(lit)] for lit in clause)
                            for clause in cnf)
            satisfying = [assignment for assignment in bits(len(occurring))
                          if cnf_value(renamed, assignment)]
            self.assertEqual(len(satisfying), 8 if value else 0)
            extracted = [circuit.restrict(assignment) for assignment in satisfying]
            self.assertEqual(set(extracted), set(bits(3)) if value else set())
            self.assertEqual(len(extracted), len(set(extracted)))

    def test_builder_canonical_topological_indices(self):
        builder = Builder(2)
        z = builder.conjunction(0, 1)
        self.assertEqual(z, 2)
        self.assertEqual(builder.conjunction(0, 1), z)
        out = builder.negate(z)
        circuit = builder.finish(out)
        self.assertEqual(circuit.wires, 4)
        for witness in bits(2):
            self.assertEqual(circuit.evaluate(witness), not (witness[0] and witness[1]))

    def test_gadget_truth_tables_with_aliases(self):
        for x in (0, 1):
            for y in (0, 1):
                circuit = Circuit(2, (Gate("and", (x, y)),), 2)
                for assignment in bits(3):
                    self.assertEqual(cnf_value(circuit.tseitin(False), assignment),
                                     assignment[2] == (assignment[x] and assignment[y]))

    def test_reject_malformed_circuits_and_assignments(self):
        with self.assertRaises(ValueError):
            Circuit(1, (Gate("not", (1,)),), 1).check()
        with self.assertRaises(ValueError):
            Circuit(1, (Gate("not", (-1,)),), 1).check()
        with self.assertRaises(ValueError):
            Circuit(0, (), 0).check()
        with self.assertRaises(ValueError):
            Circuit(1, (), 0).extend((1,))
        with self.assertRaises(ValueError):
            cnf_value(((0,),), (True,))


class TestBoundedCompiler(unittest.TestCase):
    def compare(self, machine, fixed, width, clock):
        compiled = compile_verifier(machine, fixed, width, clock)
        circuit = compiled.circuit
        cnf = circuit.tseitin()
        self.assertLessEqual(len(cnf), 3 * len(circuit.gates) + circuit.inputs + 1)
        self.assertTrue(all(1 <= len(c) <= 3 for c in cnf))
        for witness in bits(width):
            trace = simulate_trace(machine, tuple(fixed) + tuple(map(int, witness)), clock)
            values = compiled.extend_witness(witness)
            self.assertEqual(len(trace), len(compiled.snapshots))
            for snapshot, expected in zip(compiled.snapshots, trace):
                actual = snapshot.decode(values)
                self.assertEqual(actual.state, expected.state)
                self.assertEqual(actual.head, expected.head)
                for p in snapshot.positions:
                    self.assertEqual(actual.tape[p], expected.tape.get(p, BLANK))
            accepts = trace[-1].state in machine.accepting
            self.assertEqual(values[circuit.output], accepts)
            self.assertEqual(cnf_value(cnf, values), accepts)
            if accepts:
                self.assertEqual(compiled.extract_witness(values), witness)

    def test_parity_all_small_inputs_witnesses_and_clocks(self):
        machine = parity_machine()
        for fixed_width in range(2):
            for fixed in bits(fixed_width):
                for width in range(3):
                    for clock in range(fixed_width + width + 3):
                        self.compare(machine, tuple(map(int, fixed)), width, clock)

    def test_larger_witness_assignment_extension(self):
        self.compare(parity_machine(), (1, 0), 3, 6)

    def test_leftward_head_motion_writes_and_blank(self):
        transitions = {}
        for symbol in ALPHABET:
            transitions[0, symbol] = (1, 1, -1)
            transitions[1, symbol] = (2, 0, 1)
            transitions[2, symbol] = (3 if symbol == 1 else 4, symbol, 0)
        machine = TapeMachine(5, 0, frozenset({3}), frozenset({4}), transitions)
        for clock in range(6):
            self.compare(machine, (), 2, clock)

    def test_zero_clock_and_absorbing_terminal_states(self):
        for accepts in (False, True):
            machine = TapeMachine(1, 0, frozenset({0}) if accepts else frozenset(),
                                  frozenset() if accepts else frozenset({0}), {})
            for clock in (0, 1, 3):
                self.compare(machine, (), 0, clock)
                self.compare(machine, (1,), 2, clock)

    def test_corrupted_extensions_violate_gate_constraints(self):
        compiled = compile_verifier(parity_machine(), (1,), 1, 3)
        circuit = compiled.circuit
        assignment = circuit.extend((True,))
        constraints = circuit.tseitin(False)
        self.assertTrue(cnf_value(constraints, assignment))
        # Every individual auxiliary wire, including inactive intermediate wires,
        # is fixed by earlier gate values. Flipping one must violate constraints.
        for i in range(circuit.inputs, circuit.wires):
            changed = list(assignment)
            changed[i] = not changed[i]
            self.assertFalse(cnf_value(constraints, changed))

    def test_reject_invalid_machine_and_clock(self):
        incomplete = TapeMachine(1, 0, frozenset(), frozenset(), {})
        with self.assertRaises(ValueError):
            compile_verifier(incomplete, (), 0, 1)
        with self.assertRaises(ValueError):
            compile_verifier(parity_machine(), (), 0, -1)
        with self.assertRaises(ValueError):
            compile_verifier(parity_machine(), (2,), 0, 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
