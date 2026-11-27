"""The environment of tests that start axiom-fuzz: without the evaluation switches.

Every AXIOM_* variable (lib/scheduler/eval.ml lists those axiom-fuzz reads) and the OCaml runtime
parameters can change or instrument a search, so a variable exported in a contributor's shell would
change what a test checks. scrub() removes them from os.environ, which every child process
inherits; a test that needs one sets it for that run only. The OCaml tests need no such step: the
library reads no environment variable itself, and the tests pass Eval.of_env their own lookup.
"""
import os


def scrub():
    for name in [k for k in os.environ
                 if k.startswith("AXIOM_") or k in ("OCAMLRUNPARAM", "CAMLRUNPARAM")]:
        del os.environ[name]
