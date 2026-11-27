"""Rocq assumption audit: proof holes, axiom-like declarations, Print Assumptions output."""
import contextlib
import io
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(sys.argv.pop(1)).resolve().parent))
import rocq_assumptions as audit

CLOSED = "Closed under the global context\n"
CLASSIC = "Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
# Rocq 9.3.0 output for theory_refuted of a generated AVATAR proof.
STANDARD = """Axioms:
RelationalChoice.relational_choice :
  forall (A B : Type) (R : A -> B -> Prop),
  (forall x : A, exists y : B, R x y) ->
  exists R' : A -> B -> Prop,
    subrelation R' R /\\ (forall x : A, exists ! y : B, R' x y)
PropExtensionality.propositional_extensionality :
  forall P Q : Prop, P <-> Q -> P = Q
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
ClassicalUniqueChoice.dependent_unique_choice :
  forall (A : Type) (B : A -> Type) (R : forall x : A, B x -> Prop),
  (forall x : A, exists ! y : B x, R x y) ->
  exists f : forall x : A, B x, forall x : A, R x (f x)
Classical_Prop.classic : forall P : Prop, P \\/ ~ P
"""
# How a generated AVATAR proof checks its certificate (clause proofs use check_sources).
AVATAR = """Example proof_checked : Checked.avatar_check_sources visit limit budget = true.
Proof. vm_compute. reflexivity. Qed.
"""
CLEAN = """(* Admitted and Axiom inside a comment do not count. *)
Definition text := "Admitted".
Section Local.
Variable x : nat.
Hypothesis positive : 0 < x.
Lemma kept : 0 < x. Proof. exact positive. Qed.
End Local.
Module Type Order.
Parameter t : Type.
End Order.
Lemma closed : True. Proof. exact I. Qed.
Print Assumptions closed.
"""


def check(source, output, generated=None):
    """Audit one library file (and optionally one generated proof); return the exit code."""
    with tempfile.TemporaryDirectory() as root:
        library = pathlib.Path(root) / "rocq" / "A.v"
        library.parent.mkdir()
        library.write_text(source)
        library.with_name("A.v.out").write_text(output)
        argv = ["rocq_assumptions.py", root]
        if generated is not None:
            proof = pathlib.Path(root) / "Proof.v"
            proof.write_text(generated[0])
            proof.with_name("Proof.v.out").write_text(generated[1])
            argv.append(str(proof))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return audit.main(argv)


class Audit(unittest.TestCase):
    def test_sections_module_types_comments_and_closed_results_pass(self):
        self.assertEqual(check(CLEAN, CLOSED), 0)

    def test_proof_holes_fail(self):
        for hole in ["Admitted.", "admit. Qed.", "give_up. Qed."]:
            source = CLEAN + f"Lemma hole : False. Proof. {hole}\n"
            self.assertEqual(check(source, CLOSED), 1, hole)

    def test_strings_inside_comments_are_lexed_as_rocq_does(self):
        # Rocq reads "*)" here as a string inside the comment, so the comment goes on.
        quoted = '(* a quoted "*)" inside a comment *)\n'
        self.assertEqual(check(quoted + CLEAN, CLOSED), 0)
        hidden = CLEAN + quoted + "Lemma hole : 1 = 2.\nProof. Admitted.\n"
        self.assertEqual(check(hidden, CLOSED), 1)
        # Rocq rejects these, so the audit cannot have read them the same way.
        for unterminated in ["(* open comment\n", 'Definition s := "open.\n', '(* a lone " quote *)\n']:
            self.assertEqual(check(CLEAN + unterminated, CLOSED), 1, unterminated)

    def test_global_assumptions_fail(self):
        for declaration in ["Axiom bad : False.", "#[local] Axiom bad : False.", "Parameter p : nat.",
                            "Conjecture c : False.", "Variable v : nat.", "Hypothesis h : False.",
                            "Local Unset Guard Checking.",
                            "#[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.",
                            "Declare Instance bad_instance : Bad.", "#[local] Declare Instance i : C.",
                            "Time Axiom bad : False.", "Timeout 10 Axiom bad : False.",
                            "Primitive myint := #int63_type.", "Set Definitional UIP."]:
            self.assertEqual(check(CLEAN + declaration + "\n", CLOSED), 1, declaration)

    def test_print_assumptions_must_be_plain(self):
        # Redirect sends the result to a file, so the output would lack it.
        self.assertEqual(check(CLEAN + 'Redirect "out" Print Assumptions closed.\n', CLOSED), 1)
        self.assertEqual(check(CLEAN + 'Redirect "out" Check closed.\n', CLOSED), 1)
        timed = "Finished transaction in 0. secs (0.u,0.s) (successful)\n"
        self.assertEqual(check(CLEAN + "Time Print Assumptions closed.\n", CLOSED + CLOSED + timed), 1)
        # A command may span lines; its result still counts.
        self.assertEqual(check(CLEAN + "Print\n  Assumptions closed.\n", CLOSED + CLOSED), 0)

    def test_unlisted_assumptions_and_missing_results_fail(self):
        self.assertEqual(check(CLEAN, CLASSIC), 1)
        self.assertEqual(check(CLEAN, ""), 1)
        self.assertEqual(check(CLEAN, CLOSED + CLOSED), 1)

    def test_unreadable_axioms_entries_fail(self):
        # Rocq 9.3.0 output for an axiom named λ, an unguarded fixpoint, a definition
        # made under Unset Universe Checking, and a section variable.
        for output in ["Axioms:\nλ : False\n", "Axioms:\nloop is assumed to be guarded.\n",
                       "Axioms:\nuu relies on an unsafe hierarchy.\nU relies on an unsafe hierarchy.\n",
                       "Axioms:\n", "Section Variables:\nx\n: nat\n"]:
            self.assertEqual(check(CLEAN, output), 1, output)
        refuted = AVATAR + "Print Assumptions theory_refuted.\n"
        self.assertEqual(check(CLEAN, CLOSED, (refuted, STANDARD)), 0)
        self.assertEqual(check(CLEAN, CLOSED, (refuted, STANDARD + "λ : False\n")), 1)

    def test_generated_allow_list_is_per_theorem_and_avatar_only(self):
        refuted = "Print Assumptions theory_refuted.\n"
        self.assertEqual(check(CLEAN, CLOSED, (AVATAR + refuted, CLASSIC)), 0)
        self.assertEqual(check(CLEAN, CLOSED, (AVATAR + refuted, STANDARD)), 0)
        # A clause proof states theory_refuted as Checked.derives_false: closed.
        self.assertEqual(check(CLEAN, CLOSED, (refuted, CLOSED)), 0)
        self.assertEqual(check(CLEAN, CLOSED, (refuted, CLASSIC)), 1)
        self.assertEqual(check(CLEAN, CLOSED, ("(* avatar_check_sources *)\n" + refuted, CLASSIC)), 1)
        other = "Print Assumptions source_axioms_unsatisfiable.\n"
        self.assertEqual(check(CLEAN, CLOSED, (AVATAR + other, CLASSIC)), 1)
        self.assertEqual(check(CLEAN, CLOSED, ("Axiom x : False.\n" + AVATAR + refuted, CLOSED)), 1)


if __name__ == "__main__":
    unittest.main(argv=sys.argv[:1], verbosity=1)
