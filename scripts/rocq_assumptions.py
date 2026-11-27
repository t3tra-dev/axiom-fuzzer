"""Audit Rocq sources and their `Print Assumptions` output.

usage: rocq_assumptions.py BUILD_ROOT [GENERATED.v ...]

BUILD_ROOT holds the copied `rocq/` tree. Every `.v` file there and every generated
proof must have a sibling `.v.out` with the stdout of its compilation. The check fails
on proof holes and on declarations that act as axioms, and it requires each
`Print Assumptions` result to be closed or to list only assumptions allowed below.
Section variables and module type fields are arguments, not axioms.

The scan is lexical. It reads comments and strings as Rocq's lexer does and fails on
what it cannot read the same way: an unterminated comment or string, any `Redirect`,
and a `Print Assumptions` with a control modifier. In the output, a line of an
`Axioms:` block that is not `NAME : TYPE` counts as an assumption itself.
"""

import re
import sys
from pathlib import Path

# Meta-theory axioms of the standard first-order connection (Stdlib).
STANDARD = {
    "Classical_Prop.classic",
    "FunctionalExtensionality.functional_extensionality_dep",
    "PropExtensionality.propositional_extensionality",
    "RelationalChoice.relational_choice",
    "ClassicalUniqueChoice.dependent_unique_choice",
}
# Module parameters of the normalization functor (Order : WireOrder).
ORDER = {"Order.function_name", "Order.predicate_name", "Order.leb", "Order.equal", "Order.equal_sound"}
ORDER_COMPARE = {"Order.leb", "Order.equal", "Order.equal_sound"}


def allow(path, names, assumptions):
    return {(path, name): assumptions for name in names}


# (file, theorem) -> allowed assumptions. Every other result must be closed.
LIBRARY = {
    **allow(
        "rocq/Wire/Refutation.v",
        ["normalize_forward", "normalize_correct", "normalized_wire_check_sound"],
        ORDER,
    ),
    **allow(
        "rocq/Source/Refutation.v",
        [
            "source_distributive_check_sound",
            "source_definitional_check_sound",
            "source_inputs_check_sound",
            "source_inputs_avatar_check_sound",
        ],
        ORDER,
    ),
    **allow(
        "rocq/Source/Kernel.v",
        ["check_sources_sound", "check_sound", "avatar_check_sources_sound", "avatar_check_sound"],
        ORDER_COMPARE,
    ),
    **allow("rocq/Source/Kernel.v", ["check_derives_false"], {"Order.leb", "Order.equal"}),
    **allow("rocq/Source/Standard.v", ["quotient_model"], STANDARD),
    **allow(
        "rocq/Source/Standard.v",
        ["refutation_is_standard", "avatar_check_is_standard"],
        STANDARD | ORDER_COMPARE,
    ),
    **allow(
        "rocq/Logic/Completeness.v",
        ["refutation_complete"],
        {
            "Classical_Prop.classic",
            "RelationalChoice.relational_choice",
            "ClassicalUniqueChoice.dependent_unique_choice",
        },
    ),
    **allow(
        "rocq/Reference/Theory.v",
        ["enumeration_check_sound", "recursively_axiomatized_complete"],
        STANDARD,
    ),
    **allow(
        "rocq/Examples/Completeness.v",
        [
            "StandardConnection.refutation_is_standard",
            "StandardConnection.avatar_check_is_standard",
            "Complete.check_iff_standard",
            "Complete.accepted_eventually_found",
            "Enumerated.check_iff_enumerated",
        ],
        STANDARD,
    ),
}
# Generated proofs: theorem name -> allowed assumptions. Only an AVATAR proof, whose
# proof_checked runs avatar_check_sources, states theory_refuted in standard natural
# deduction and keeps the Stdlib meta-theory axioms of that connection. Every other
# generated result, including every clause and natural proof, must be closed.
AVATAR_GENERATED = {"theory_refuted": STANDARD}
AVATAR = re.compile(r"\bavatar_check_sources\b")

HOLES = re.compile(r"\b(Admitted|admit|give_up|Admit|bypass_check)\b")
UNSAFE = re.compile(r"^(?:Unset (Guard|Positivity|Universe) Checking|Set Definitional UIP)\b")
AXIOMS = re.compile(
    r"^(Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures|Declare (Module|Instance)|Primitive)\b"
)
LOCALS = re.compile(r"^(Hypothesis|Hypotheses|Variable|Variables|Context)\b")
PREFIX = re.compile(
    r"^(?:[\s\-+*{}]+|#\[[^\]]*\]\s*"
    r"|(?:Local|Global|Polymorphic|Monomorphic|Cumulative|NonCumulative|Program|Private)\s+)"
)
# Control modifiers run the command after them; strings are already stripped to "".
CONTROL = re.compile(r'^(Time|Instructions|Profile|Fail|Succeed|Timeout|Redirect)\b\s*(?:\d+\s*|""\s*)?')
PRINT = re.compile(r"\bPrint Assumptions\b")


def strip(text, label, errors):
    """Remove (nested) comments and string contents as Rocq's lexer reads them.

    Line breaks are kept. Rocq lexes strings inside comments too, so a quoted "*)"
    does not end a comment. An unterminated string or comment fails the audit.
    """
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text[i] == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and text[j + 1 : j + 2] != '"'):
                j += 2 if text[j] == '"' else 1
            if j >= n:
                errors.append(f"{label}:{text.count(chr(10), 0, i) + 1}: unterminated string")
            out.append(('""' if depth == 0 else "") + "\n" * text.count("\n", i, j))
            i = j + 1
        elif text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        else:
            if depth == 0 or text[i] == "\n":
                out.append(text[i])
            i += 1
    if depth:
        errors.append(f"{label}: unterminated comment")
    return "".join(out)


def sentences(text):
    """Yield each sentence as written (with attributes), its command without prefixes or
    control modifiers and with single spaces, the modifiers, and its first line."""
    for m in re.finditer(r"(.*?)\.(?=\s|$)", text, re.S):
        raw = body = m.group(1)
        controls = []
        while True:
            control = CONTROL.match(body)
            if control:
                controls.append(control.group(1))
                body = body[control.end() :]
                continue
            shorter = PREFIX.sub("", body, count=1)
            if shorter == body:
                break
            body = shorter
        start = m.start() + len(raw) - len(raw.lstrip())
        yield raw, " ".join(body.split()), controls, text.count("\n", 0, start) + 1


def scan(path, label, errors):
    """Reject proof holes and axiom-like declarations; return Print Assumptions names."""
    text = strip(path.read_text(), label, errors)
    stack, printed = [], []
    for raw, sentence, controls, line in sentences(text):
        where = f"{label}:{line}"
        if HOLES.search(raw) or UNSAFE.match(sentence):
            errors.append(f"{where}: proof hole or unchecked declaration: {sentence[:60]!r}")
        if "Redirect" in controls:
            errors.append(f"{where}: Redirect hides output from the audit: {sentence[:60]!r}")
        words = sentence.split()
        if not words:
            continue
        kinds = [kind for kind, _ in stack]
        if words[0] == "Section" and len(words) > 1:
            stack.append(("section", words[1]))
        elif words[0] == "Module" and ":=" not in sentence and len(words) > 1:
            kind, name = ("type", words[2]) if words[1] == "Type" else ("module", words[1])
            if name in ("Import", "Export") and len(words) > 2:
                name = words[2]
            stack.append((kind, name))
        elif words[0] == "End" and len(words) > 1:
            while stack and stack.pop()[1] != words[1]:
                pass
        elif AXIOMS.match(sentence) and "type" not in kinds:
            errors.append(f"{where}: global assumption {sentence[:60]!r}")
        elif LOCALS.match(sentence) and not ({"section", "type"} & set(kinds)):
            errors.append(f"{where}: declaration outside a section {sentence[:60]!r}")
        elif PRINT.search(sentence):
            # A modifier would move or interleave the result (Redirect, Time, Fail, ...).
            if controls or not sentence.startswith("Print Assumptions "):
                errors.append(f"{where}: Print Assumptions must be a plain command: {sentence[:60]!r}")
            else:
                printed.append(sentence.split(" ", 2)[2])
    return printed


CLOSED = "Closed under the global context"
# Section headers of a result: Axioms:, Section Variables:, Opaque constants:, Theory:, ...
HEADER = re.compile(r"^[A-Z][A-Za-z]*(?: [A-Za-z]+)*:$")
# Phrases of assumption entries other than `NAME : TYPE` (guard, positivity, universes, UIP).
STRAY = re.compile(r"assumed|relying on|relies on|impredicative|collapsed")


def results(output):
    """Parse Print Assumptions results: a set of assumptions each (empty when closed).

    An `Axioms:` entry is `NAME : TYPE`, continued on indented lines. Any other line in
    the block, such as `loop is assumed to be guarded.`, is kept whole as an assumption,
    so it never matches an allow-list. The block ends at the next result or header; other
    output right after it is read as entries and fails the same way. Other headers
    (`Section Variables:`, `Opaque constants:`, ...) and stray assumption lines become
    results of their own, which the count or the allow-list then rejects.
    """
    lines, blocks, i = output.splitlines(), [], 0
    while i < len(lines):
        line = lines[i]
        if line == CLOSED:
            blocks.append(set())
        elif line == "Axioms:":
            names = set()
            while i + 1 < len(lines) and lines[i + 1] != CLOSED and not HEADER.match(lines[i + 1]):
                i += 1
                entry = lines[i]
                if entry.strip() and not entry[0].isspace():
                    m = re.match(r"(\S+) :(?:\s|$)", entry)
                    names.add(m.group(1) if m else entry)
            blocks.append(names or {line})
        elif HEADER.match(line) or STRAY.search(line):
            blocks.append({line})
        i += 1
    return blocks


def qualified(name):
    """Stdlib axioms print unqualified where their module is imported."""
    for full in STANDARD:
        if name == full.rsplit(".", 1)[1]:
            return full
    return name


def audit(path, label, allowed, errors):
    printed = scan(path, label, errors)
    out = path.with_name(path.name + ".out")
    if not out.exists():
        errors.append(f"{label}: missing compiler output {out.name}")
        return 0
    blocks = results(out.read_text())
    if len(blocks) != len(printed):
        errors.append(f"{label}: {len(printed)} Print Assumptions but {len(blocks)} results")
        return 0
    for name, found in zip(printed, blocks):
        extra = {qualified(x) for x in found} - allowed(name)
        if extra:
            errors.append(f"{label}: {name} assumes {', '.join(sorted(extra))}")
    return len(blocks)


def main(argv):
    root, generated = Path(argv[1]), [Path(p) for p in argv[2:]]
    errors, checked = [], 0
    for path in sorted((root / "rocq").rglob("*.v")):
        label = str(path.relative_to(root))
        checked += audit(path, label, lambda n, f=label: LIBRARY.get((f, n), set()), errors)
    avatar = 0
    for path in generated:
        # Code only: a comment or string cannot make a proof count as AVATAR.
        table = AVATAR_GENERATED if AVATAR.search(strip(path.read_text(), path.name, [])) else {}
        avatar += bool(table)
        checked += audit(path, path.name, lambda n, t=table: t.get(n, set()), errors)
    if errors:
        print("Rocq assumption audit failed:", *errors, sep="\n  ", file=sys.stderr)
        return 1
    print(
        f"Rocq assumptions: {checked} Print Assumptions results match the allow-list "
        f"({avatar} of {len(generated)} generated proofs are AVATAR)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
