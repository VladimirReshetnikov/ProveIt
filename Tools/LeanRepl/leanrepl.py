#!/usr/bin/env python3
"""leanrepl — a GHCi-style interactive REPL for Lean 4.

Front-end on top of LeanInteract (https://github.com/augustepoiroux/LeanInteract),
which manages the Lean REPL backend (https://github.com/leanprover-community/repl).

Usage:
  python leanrepl.py                      # auto-detect enclosing Lake project
  python leanrepl.py --project C:/ProveIt # REPL inside a specific Lake project
  python leanrepl.py --plain              # bare Lean, no project
  python leanrepl.py -i Mathlib.Tactic    # start with imports
  python leanrepl.py file.lean            # load a file at startup
"""

from __future__ import annotations

import argparse
import datetime
import os
import re
import sys
import time
from pathlib import Path

# Lean output is Unicode-heavy; the Windows console defaults to a legacy
# codepage, so force UTF-8 on all standard streams.
for _stream in (sys.stdout, sys.stderr, sys.stdin):
    if hasattr(_stream, "reconfigure") and (_stream.encoding or "").lower() not in ("utf-8", "utf8"):
        _stream.reconfigure(encoding="utf-8", errors="replace")

# ---------------------------------------------------------------------------
# Terminal colors
# ---------------------------------------------------------------------------

USE_COLOR = sys.stdout.isatty() and os.environ.get("NO_COLOR") is None
if USE_COLOR and os.name == "nt":
    # The classic Windows console needs virtual-terminal processing switched
    # on before ANSI escapes render; fall back to plain text if that fails.
    try:
        import ctypes
        _k32 = ctypes.windll.kernel32
        _handle = _k32.GetStdHandle(-11)  # STD_OUTPUT_HANDLE
        _mode = ctypes.c_uint32()
        if (not _k32.GetConsoleMode(_handle, ctypes.byref(_mode))
                or not _k32.SetConsoleMode(_handle, _mode.value | 0x0004)):
            USE_COLOR = False
    except Exception:  # noqa: BLE001
        USE_COLOR = False


def _c(code: str, text: str) -> str:
    return f"\x1b[{code}m{text}\x1b[0m" if USE_COLOR else text


def red(t: str) -> str:
    return _c("31", t)


def yellow(t: str) -> str:
    return _c("33", t)


def green(t: str) -> str:
    return _c("32", t)


def cyan(t: str) -> str:
    return _c("36", t)


def dim(t: str) -> str:
    return _c("2", t)


def bold(t: str) -> str:
    return _c("1", t)


# ---------------------------------------------------------------------------
# Session transcripts
# ---------------------------------------------------------------------------

ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


class Transcript:
    """Writes a plain-text (ANSI-stripped) copy of the whole session to a file.
    Output is captured by teeing sys.stdout; input lines are appended
    explicitly by the read loop (interactive input never passes through
    stdout)."""

    def __init__(self, path: Path):
        self.path = path
        self._file = open(path, "a", encoding="utf-8")
        self._real_stdout = None
        stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self._file.write(f"-- LeanRepl transcript started {stamp}\n")
        self._file.flush()

    def install(self):
        self._real_stdout = sys.stdout
        sys.stdout = _TeeStream(self._real_stdout, self)

    def uninstall(self):
        if self._real_stdout is not None:
            sys.stdout = self._real_stdout
            self._real_stdout = None

    def write_raw(self, text: str):
        self._file.write(ANSI_RE.sub("", text))
        self._file.flush()

    def write_input(self, prompt: str, line: str, timestamp: bool = False):
        if timestamp:
            self.write_raw(f"[{datetime.datetime.now().strftime('%H:%M:%S')}]\n")
        self.write_raw(f"{prompt}{line}\n")

    def close(self):
        self.uninstall()
        stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self._file.write(f"-- LeanRepl transcript ended {stamp}\n")
        self._file.close()


class _TeeStream:
    """Forwards writes to the real stdout and appends them to the transcript."""

    def __init__(self, real, transcript: Transcript):
        self._real = real
        self._transcript = transcript

    def write(self, s: str):
        self._real.write(s)
        self._transcript.write_raw(s)
        return len(s)

    def flush(self):
        self._real.flush()

    def __getattr__(self, name):  # encoding, isatty, fileno, ...
        return getattr(self._real, name)


def default_transcript_path() -> Path:
    name = datetime.datetime.now().strftime("leanrepl-%Y%m%d-%H%M%S.log")
    return Path.cwd() / name


# ---------------------------------------------------------------------------
# Input classification
# ---------------------------------------------------------------------------

# First tokens that mark input as a top-level command/declaration to be run
# verbatim (rather than an expression to #eval / #check).
DECL_KEYWORDS = {
    "abbrev", "add_decl_doc", "alias", "attribute", "axiom", "binder_predicate",
    "builtin_initialize", "class", "declare_syntax_cat", "def", "deriving",
    "elab", "elab_rules", "end", "example", "export", "extends", "gen_injective_theorems",
    "import", "in", "include", "inductive", "infix", "infixl", "infixr", "initialize",
    "instance", "lemma", "local", "macro", "macro_rules", "mutual", "namespace",
    "noncomputable", "notation", "omit", "opaque", "open", "partial", "postfix",
    "prefix", "private", "protected", "recall", "run_cmd", "run_elab", "scoped",
    "section", "set_option", "show_panel_widgets", "structure", "syntax",
    "theorem", "unif_hint", "universe", "unsafe", "variable", "variables",
}

CONTINUATION_ENDINGS = (
    ":=", "=>", "by", "do", "then", "else", "where", ",", "|", "fun", "with",
    "←", "<-", "→", "->", "↔", "<->", "∧", "∨", "+", "*", "/", "(", "[", "{",
    "⟨", "«", ":", ";", "·", "$", "from", "have", "let", "in", "match",
)

OPEN_BRACKETS = "([{⟨"
CLOSE_BRACKETS = ")]}⟩"
BRACKET_MAP = dict(zip(CLOSE_BRACKETS, OPEN_BRACKETS))


def strip_strings_and_comments(text: str) -> str:
    """Remove string literals, char literals and comments so bracket counting
    is not confused by them.  Rough but adequate for balance heuristics."""
    out = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == '"':  # string literal
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif ch == "'" and i + 2 < n and (text[i + 1] == "\\" or text[i + 2] == "'"):
            # char literal like 'a' or '\n'
            i += 3 if text[i + 1] != "\\" else 4
        elif text.startswith("--", i):  # line comment
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("/-", i):  # block comment (nested)
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def bracket_balance(text: str) -> int:
    """Net count of unclosed brackets (only counts, ignores mismatch kinds)."""
    clean = strip_strings_and_comments(text)
    bal = 0
    for ch in clean:
        if ch in OPEN_BRACKETS:
            bal += 1
        elif ch in CLOSE_BRACKETS:
            bal -= 1
    return bal


def in_open_block_comment(text: str) -> bool:
    clean_len_text = text
    depth = 0
    i = 0
    n = len(clean_len_text)
    while i < n:
        if clean_len_text.startswith("/-", i):
            depth += 1
            i += 2
        elif clean_len_text.startswith("-/", i):
            depth = max(0, depth - 1)
            i += 2
        else:
            i += 1
    return depth > 0


def needs_continuation(text: str) -> bool:
    """Heuristic: does this input look syntactically incomplete?"""
    if in_open_block_comment(text):
        return True
    if bracket_balance(text) > 0:
        return True
    stripped = strip_strings_and_comments(text).rstrip()
    if not stripped:
        return False
    for ending in CONTINUATION_ENDINGS:
        if stripped.endswith(ending):
            # avoid treating identifiers ending in keyword letters as keywords
            if ending.isalpha() or ending in ("<-", ":="):
                tail = stripped[-len(ending) - 1: -len(ending)]
                if tail and (tail.isalnum() or tail in "_.'"):
                    continue
            return True
    return False


def first_token(text: str) -> str:
    m = re.match(r"\s*([#@\[]*[A-Za-z_][A-Za-z0-9_?!']*|#\w+|@\[)", text)
    return m.group(1) if m else ""


def is_declaration(text: str) -> bool:
    t = text.lstrip()
    if t.startswith("#") or t.startswith("@[") or t.startswith("--") or t.startswith("/-"):
        return True
    tok = first_token(t)
    return tok in DECL_KEYWORDS


# ---------------------------------------------------------------------------
# Help for built-ins and keywords that are not constants in the environment
# (content adapted from the Lean 4 manual and Theorem Proving in Lean 4)
# ---------------------------------------------------------------------------

BUILTIN_HELP: dict[str, str] = {
    "imax": """`imax` is an operation of Lean's built-in *universe level* arithmetic,
not a constant in the environment — which is why `#check imax` fails.
Universe levels form their own tiny language: `0`, `u+1`, `max u v`,
`imax u v`. `imax u v` equals `0` when `v = 0`, and `max u v` otherwise.
It appears in the universe of dependent function types:
  (x : Sort u) → Sort v  :  Sort (imax u v)
so a function into a proposition (`v = 0`) is itself a proposition —
this is what makes `Prop` impredicative: `∀ p : Prop, p : Prop`.
Universe expressions can only occur inside `Sort u` / `Type u`.""",
    "Sort": """`Sort u` is the universe of types at level `u`; it is primitive syntax,
not a constant. `Prop` is `Sort 0` and `Type u` is `Sort (u + 1)`.
A bare `Sort` needs a level: try `:t Sort 0` or `:t Sort (u + 1)`.
Universe levels are built from `0`, `u+1`, `max u v`, `imax u v`.""",
    "fun": """`fun` (or `λ`) is the keyword introducing an anonymous function; it is
syntax, not a constant. Examples:
  fun x => x + 1
  fun (x : Nat) (y : Nat) => x * y
  fun ⟨a, b⟩ => a   -- pattern-matching binder
`fun x => e : α → β` when `e : β` given `x : α`.""",
    "→": """`→` (ASCII `->`) is the function arrow, primitive syntax for the
(non-dependent) function type — shorthand for `(_ : α) → β`. It is
right-associative: `α → β → γ` is `α → (β → γ)`. The dependent form
binds a name: `(x : α) → p x` (same as `∀ x : α, p x`). To inspect it
as an operator, apply section notation: `:t (· → ·)`.""",
    "∀": """`∀` (keyword `forall`) is the universal quantifier binder. It is
notation for the dependent function type: `∀ x : α, p x` is exactly
`(x : α) → p x`; a proof of it is a function mapping each `x` to a
proof of `p x`. Its universe is `Sort (imax u v)` (see `:info imax`).""",
    "∃": """`∃` is binder notation for the inductive predicate `Exists`:
`∃ x : α, p x` unfolds to `Exists fun x => p x`. Introduce it with
`⟨witness, proof⟩`, eliminate with `obtain ⟨x, hx⟩ := h`.
See `:info Exists`.""",
    "by": """`by` is a keyword that enters *tactic mode*: `by tac` elaborates the
tactic block `tac` to produce a term of the expected type, e.g.
  theorem t : 2 + 2 = 4 := by rfl
It is syntax, not a term — it only makes sense where a term of a known
type is expected.""",
    "do": """`do` is a keyword introducing monadic do-notation: sequencing with
`let x ← action`, early `return`, `if`/`for`/`try` blocks. A `do` block
elaborates to `bind`/`pure` calls in the ambient monad, e.g.
  def main : IO Unit := do
    let line ← (← IO.getStdin).getLine
    IO.println line""",
    "match": """`match` is the pattern-matching keyword:
  match xs with
  | []      => ...
  | x :: r  => ...
It is compiled to auxiliary matcher functions built on recursors, so it
is syntax rather than a constant you can `#check`.""",
    "where": """`where` is a keyword attaching auxiliary definitions to a declaration
(visible in its body), and also introduces the field/constructor block
of `structure`/`inductive` declarations:
  def f (n : Nat) : Nat := g n + 1
    where g (k : Nat) := 2 * k""",
    "let": """`let` is a keyword introducing a local definition in a term or do-block:
`let x := e; body` (or on separate lines). Unlike `fun`-abstraction,
`x` is definitionally transparent in `body`.""",
    "have": """`have` is a keyword stating an intermediate fact in term or tactic
mode: `have h : p := proof` makes `h : p` available afterwards. Unlike
`let`, the definition is opaque — only the type matters.""",
    "show": """`show` is a keyword annotating the expected type: `show t from e` (or
`show t; tac` in tactic mode) checks/changes the goal to the
definitionally equal `t`.""",
    "calc": """`calc` is the keyword for chained calculational proofs:
  calc a = b := by ...
       _ = c := by ...
Steps are glued with `Trans` instances.""",
    ":=": """`:=` is the definition/assignment token: it separates a declaration's
signature from its body (`def f : T := e`), appears in `let`/`have`,
and in structure-instance fields (`{ x := 1 }`). It is punctuation, not
an operator.""",
    "=>": """`=>` is the token separating a binder or pattern from its body: in
`fun x => e`, in `match` arms (`| pat => e`), and in tactic
alternatives. Not to be confused with implication, which is `→`.""",
    "←": """`←` (ASCII `<-`) is punctuation with two roles: in do-notation,
`let x ← action` binds the result of a monadic action; inside a do
expression `(← action)` inlines it. In `rw [← h]` it rewrites with
equation `h` right-to-left.""",
    "|": """`|` separates alternatives: constructors in `inductive ... where`,
arms of `match` (and equation-style `def`), and `<|>` alternatives in
tactics use `first | t₁ | t₂`. `p₁ | p₂` inside patterns does not
exist in Lean 4 — write separate arms.""",
    "@": """`@f` is the *explicit application* prefix: it turns all implicit
arguments of `f` into explicit ones, e.g. `@id Nat 3`. Useful with
`:t @f` to see the full signature including implicits.""",
    "_": """`_` is a placeholder (hole): Lean infers the term or type from
context. In proofs, `?h` named holes create goals; in patterns `_`
matches anything without binding a name.""",
    "·": """`·` is the section/placeholder dot: `(· + 1)` is `fun x => x + 1`,
`(· → ·)` is `fun a b => a → b`. Each `·` inside the closest
parentheses becomes a fresh bound variable, in order.""",
    "⟨": """`⟨e₁, e₂, ...⟩` is the *anonymous constructor*: it builds a value of
any expected single-constructor type (pairs, `And`, `Exists`,
structures): `(⟨1, rfl⟩ : ∃ n, n = 1)`. In patterns it destructures.""",
}

BUILTIN_ALIASES: dict[str, str] = {
    "->": "→", "forall": "∀", "exists": "∃",
    "λ": "fun", "lambda": "fun",
    "<-": "←", "⟩": "⟨", "⟨⟩": "⟨",
}


def builtin_info(token: str) -> str | None:
    """Help text if `token` is a known built-in / keyword, else None."""
    t = token.strip()
    t = BUILTIN_ALIASES.get(t, t)
    return BUILTIN_HELP.get(t)


def print_builtin_info(token: str) -> bool:
    text = builtin_info(token)
    if text is None:
        return False
    print(cyan(f"built-in: {token.strip()}"))
    for line in text.splitlines():
        print("  " + line)
    return True


def indent_def_body(data: str) -> str | None:
    """#print emits definition bodies at column 0 after the ':=' line; indent
    them two spaces, Lean-style. Returns None if the shape doesn't match."""
    lines = data.splitlines()
    header_end = next((i for i, ln in enumerate(lines)
                       if ln.rstrip().endswith(":=")), None)
    if header_end is None or header_end == len(lines) - 1:
        return None
    body = lines[header_end + 1:]
    if all(ln.startswith(" ") or not ln.strip() for ln in body):
        return None  # already indented
    return "\n".join(lines[:header_end + 1]
                     + [("  " + ln if ln.strip() else ln) for ln in body])


def format_info(data: str) -> str | None:
    """Reformat `#print` output for inductives/structures/classes as a valid
    Lean declaration, e.g.

        inductive Nat : Type          inductive Nat : Type where
        number of parameters: 0   →     | zero : Nat
        constructors:                   | succ : Nat → Nat
        Nat.zero : Nat
        Nat.succ : Nat → Nat

    Returns None when the text is not in that shape (defs, theorems, ...)."""
    lines = data.splitlines()
    nparams_idx = next((i for i, ln in enumerate(lines)
                        if re.fullmatch(r"number of parameters: \d+", ln.strip())), None)
    if nparams_idx is None or nparams_idx == 0:
        return None
    header = lines[:nparams_idx]
    m = re.match(r"^(?:class inductive|inductive|structure|class)\s+([^\s({:]+)",
                 header[0])
    if not m:
        return None
    full_name = re.sub(r"\.\{[^}]*\}?$", "", m.group(1)).rstrip(".")
    prefix = full_name + "."

    def strip_prefix(s: str) -> str:
        return s[len(prefix):] if s.startswith(prefix) else s

    ctors: list[str] = []      # rendered "| name : type" lines
    fields: list[str] = []     # rendered "name : type" lines
    struct_ctor: str | None = None
    section = None
    for ln in lines[nparams_idx + 1:]:
        s = ln.strip()
        if s == "constructors:":
            section = "ctors"
        elif s == "fields:":
            section = "fields"
        elif s == "constructor:":
            section = "ctor"
        elif not s:
            continue
        elif section == "ctors":
            if ln.startswith(" ") and ctors:   # wrapped continuation line
                ctors.append("    " + s)
            else:
                ctors.append("| " + strip_prefix(s))
        elif section == "fields":
            if re.match(r"^\s{3,}", ln) and fields:  # deeper indent: continuation
                fields.append("  " + s)
            else:
                fields.append(strip_prefix(s))
        elif section == "ctor":
            if struct_ctor is None:
                name = strip_prefix(s).split(".", 1)[0].split(" ", 1)[0].split("{", 1)[0]
                struct_ctor = name
        else:
            return None  # unrecognized shape; show the original text
    out = list(header)
    out[-1] = out[-1] + " where"
    if struct_ctor is not None and struct_ctor != "mk":
        out.append("  " + struct_ctor + " ::")
    out += ["  " + c for c in ctors]
    out += ["  " + f for f in fields]
    return "\n".join(out)


# ---------------------------------------------------------------------------
# The REPL
# ---------------------------------------------------------------------------

HELP = f"""
Enter Lean declarations (def, theorem, ...) or expressions (evaluated with #eval,
falling back to #check).  Multi-line input continues automatically when a line is
syntactically incomplete; finish with an empty line.  Use :{{ and :}} for explicit
multi-line blocks.

Commands (GHCi-style):
  :help, :h, :?            show this help
  :quit, :q                exit the REPL
  :type EXPR, :t EXPR      show the type of EXPR       (#check)
  :info NAME, :i NAME      show the definition of NAME (#print)
  :load FILE, :l FILE      reset the session and load a .lean file
  :reload, :r              reload the last loaded file
  :import MOD              add an import (rebuilds the session)
  :imports                 list active imports
  :browse [NAMESPACE]      list declarations in a namespace or the session
  :set OPT VAL             set_option OPT VAL (persists in the session)
  :undo                    revert the last state-changing command
  :reset                   clear all definitions (keeps imports)
  :history                 show state-changing commands of this session
  :env                     show the current environment id
  :time                    toggle per-command timing
  :transcript [FILE|on|off] record a full transcript of the session to a file
  :timestamps [on|off]     timestamp each command in the transcript
  :pickle FILE             save the current environment to FILE (.olean)
  :unpickle FILE           restore an environment from FILE
  :! CMD                   run a shell command
Any other :-prefixed or #-prefixed Lean command (e.g. #eval, #check, #print
axioms) can be entered directly.
"""

BANNER = r"""
  __                          ___
 / /  ___ ___ ____  ______ __/ _ \___ ___  / /
/ /__/ -_) _ `/ _ \/ __/ // / , _/ -_) _ \/ /
\____|__/\_,_/_//_/_/  \_, /_/|_|\___/ .__/_/
                      /___/         /_/
"""


class LeanRepl:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.show_time = args.time
        self.timeout: float | None = args.timeout if args.timeout > 0 else None
        self.imports: list[str] = []
        for imp in args.imports or []:
            for part in imp.split(","):
                part = part.strip()
                if part:
                    self.imports.append(part)
        self.history: list[str] = []  # state-changing commands (excludes imports)
        self.env_stack: list[int | None] = []
        self.cur_env: int | None = None
        self.base_env: int | None = None  # env right after imports
        self.loaded_file: Path | None = None
        self.server = None
        self.config = None
        self.transcript: Transcript | None = None
        self.timestamps: bool = args.timestamps

    # -- server ------------------------------------------------------------

    def start(self):
        from lean_interact import AutoLeanServer, LeanREPLConfig
        from lean_interact.project import LocalProject

        t0 = time.time()
        kwargs = {"verbose": self.args.verbose}
        self.project_dir: Path | None = None
        project_dir = None
        if self.args.plain:
            pass
        elif self.args.project:
            project_dir = Path(self.args.project).resolve()
        else:
            project_dir = self.find_project(Path.cwd())
        if project_dir is not None:
            print(dim(f"Using Lake project: {project_dir}"))
            if not self.is_built_project(project_dir):
                print(yellow("warning: ") + f"{project_dir} has no .lake build — "
                      "the backend may fail or try to fetch dependencies. "
                      "Run `lake build` there, or point --project at a built checkout.")
            kwargs["project"] = LocalProject(directory=str(project_dir), auto_build=False)
            self.project_dir = project_dir
        else:
            lean_version = self.args.lean_version or "v4.32.0"
            print(dim(f"No Lake project found; using plain Lean {lean_version}"))
            kwargs["lean_version"] = lean_version

        print(dim("Preparing Lean REPL backend (first run may download and build it)..."))
        self.config = LeanREPLConfig(**kwargs)
        # The default memory guard (80% of total RAM) is too aggressive on
        # machines with a high baseline usage; only refuse near exhaustion.
        self.server = AutoLeanServer(self.config, max_total_memory=0.98,
                                     max_process_memory=None)
        print(dim(f"Lean REPL ready in {time.time() - t0:.1f}s "
                  f"(Lean {self.server.lean_version or 'unknown'})"))

        # First contact with the backend happens lazily; probe now so a broken
        # setup surfaces as a clear message instead of a traceback later.
        t0 = time.time()
        try:
            probe = self.run_cmd("#eval (0 : Nat)", env=None)
            if is_error(probe):
                raise RuntimeError(probe.message)
        except KeyboardInterrupt:
            raise
        except Exception as e:  # noqa: BLE001
            print(red("The Lean backend failed to start:"))
            print(str(e))
            print(yellow("hints: ") + "make sure the project is built (`lake build`), "
                  "check available memory, or clear the LeanInteract cache "
                  "(`clear-lean-cache`).")
            raise SystemExit(1) from e
        print(dim(f"Backend responding ({time.time() - t0:.1f}s)"))

        if self.imports:
            self.rebuild_base_env()

    # The backend REPL silently ignores imports it cannot resolve, so check
    # module availability on the Python side and warn the user.
    TOOLCHAIN_PREFIXES = ("Init", "Std", "Lean")

    def module_available(self, mod: str) -> bool:
        if mod.split(".", 1)[0] in self.TOOLCHAIN_PREFIXES:
            return True
        if self.project_dir is None:
            return False  # plain mode: only the toolchain library exists
        rel = Path(*mod.split("."))
        roots = [self.project_dir / ".lake" / "build" / "lib" / "lean"]
        pkgs = self.project_dir / ".lake" / "packages"
        if pkgs.is_dir():
            roots += [p / ".lake" / "build" / "lib" / "lean" for p in pkgs.iterdir()]
        return any((r / rel.parent / (rel.name + ".olean")).exists() for r in roots)

    def warn_missing_modules(self, mods: list[str]):
        for m in mods:
            if not self.module_available(m):
                hint = (f"run `lake build` in {self.project_dir}" if self.project_dir
                        else "plain mode has no project modules; try --project")
                print(yellow("warning: ") +
                      f"module {m} not found in the build tree — the backend will "
                      f"silently ignore it ({hint})")

    @staticmethod
    def is_built_project(d: Path) -> bool:
        return (d / ".lake" / "build" / "lib" / "lean").is_dir()

    @staticmethod
    def find_project(start: Path) -> Path | None:
        """Nearest enclosing Lake project that has been built; falls back to
        the nearest project of any kind (e.g. a git worktree of a built
        checkout has a lakefile but no .lake build of its own)."""
        candidates = [d for d in [start, *start.parents]
                      if (d / "lakefile.toml").exists() or (d / "lakefile.lean").exists()]
        for d in candidates:
            if LeanRepl.is_built_project(d):
                return d
        return candidates[0] if candidates else None

    def run_cmd(self, code: str, env: int | None, cache: bool = False):
        """Run a command in the given environment. Returns response or LeanError."""
        from lean_interact import Command
        return self.server.run(
            Command(cmd=code, env=env),
            timeout=self.timeout,
            add_to_session_cache=cache,
        )

    # -- environment management --------------------------------------------

    def rebuild_base_env(self):
        """(Re)create the base environment containing all imports, then replay
        the session history on top of it."""
        if self.imports:
            print(dim(f"Importing: {', '.join(self.imports)} ..."))
            self.warn_missing_modules(self.imports)
            t0 = time.time()
            code = "\n".join(f"import {m}" for m in self.imports)
            res = self.run_cmd(code, env=None, cache=True)
            if self.print_response(res, show_env_error=True):
                # import failed: keep previous state
                return False
            # A failed import yields a silently *empty* environment (not even
            # core notation); probe for that.
            probe = self.run_cmd("example : True := True.intro", env=res.env)
            if is_error(probe) or has_errors(probe):
                print(red("import failed: ") +
                      "the resulting environment is unusable (a module in the "
                      "import list could not be loaded)")
                self.drop_from_cache(res)
                return False
            self.base_env = res.env
            print(dim(f"Imports ready in {time.time() - t0:.1f}s"))
        else:
            self.base_env = None
        return self.replay_history()

    def replay_history(self) -> bool:
        env = self.base_env
        ok = True
        for i, code in enumerate(self.history):
            res = self.run_cmd(code, env=env, cache=True)
            if is_error(res) or has_errors(res):
                print(red(f"Replay failed at history item {i + 1}:"))
                print(dim(code))
                self.print_response(res, show_env_error=True)
                self.history = self.history[:i]
                ok = False
                break
            env = res.env
        self.cur_env = env
        self.env_stack.clear()
        return ok

    # -- response printing --------------------------------------------------

    def print_response(self, res, show_env_error: bool = False,
                       transform=None) -> bool:
        """Print messages/sorries. Returns True if there were errors.
        `transform` optionally rewrites info-message text (returning None to
        leave it unchanged)."""
        from lean_interact.interface import LeanError

        if isinstance(res, LeanError):
            print(red("REPL error: ") + res.message)
            return True
        errored = False
        for msg in res.messages:
            text = msg.data.rstrip()
            if transform is not None and msg.severity == "info":
                text = transform(text) or text
            if msg.severity == "error":
                errored = True
                print(red("error: ") + text)
            elif msg.severity == "warning":
                if text.startswith("declaration uses"):
                    continue  # redundant with the goal display below
                print(yellow("warning: ") + text)
            else:
                print(text)
        for s in getattr(res, "sorries", None) or []:
            goal = (s.goal or "").rstrip()
            print(cyan("sorry") + dim(f" (proof state {s.proof_state})"))
            for line in goal.splitlines():
                print("  " + line)
        return errored

    # -- input handling ------------------------------------------------------

    def read_input(self, prompt_fn) -> str | None:
        """Read one logical (possibly multi-line) input. None on EOF."""
        try:
            line = prompt_fn(self.prompt())
        except EOFError:
            return None
        if line is None:
            return None
        if line.strip() == ":{":
            lines = []
            while True:
                try:
                    nxt = prompt_fn(self.cont_prompt())
                except EOFError:
                    break
                if nxt.strip() == ":}":
                    break
                lines.append(nxt)
            return "\n".join(lines)
        if line.startswith(":") and not line.startswith(":{"):
            return line  # REPL commands are single-line
        # Once multi-line mode is entered, only a blank line submits (Python
        # REPL style) — completeness heuristics cannot tell whether another
        # `| ctor` or structure field is coming.
        buf = [line]
        if needs_continuation(line):
            while True:
                try:
                    nxt = prompt_fn(self.cont_prompt())
                except EOFError:
                    break
                if nxt.strip() == "":
                    break
                buf.append(nxt)
        return "\n".join(buf)

    def prompt(self) -> str:
        return "λ> "

    def cont_prompt(self) -> str:
        return "…> "

    # -- transcripts ---------------------------------------------------------

    def transcript_start(self, path: str | None):
        if self.transcript is not None:
            print(dim(f"already recording to {self.transcript.path}"))
            return
        p = Path(path).expanduser().resolve() if path else default_transcript_path()
        try:
            self.transcript = Transcript(p)
        except OSError as e:
            print(red(f"cannot open transcript file: {e}"))
            return
        self.transcript.install()
        extra = " (with per-command timestamps)" if self.timestamps else ""
        print(dim(f"recording transcript to {p}{extra}"))

    def transcript_stop(self):
        if self.transcript is None:
            print(dim("transcript is not active"))
            return
        p = self.transcript.path
        self.transcript.close()
        self.transcript = None
        print(dim(f"transcript saved to {p}"))

    def wrap_prompt(self, prompt_fn, echoes_via_stdout: bool):
        """Wrap an input function so prompts and typed lines land in the
        transcript (interactive input bypasses the stdout tee)."""
        def fn(p: str) -> str:
            is_main = p == self.prompt()
            if (self.transcript is not None and echoes_via_stdout
                    and self.timestamps and is_main):
                # prompt+line will be captured via the stdout tee; only the
                # timestamp needs writing, and it must precede the prompt
                self.transcript.write_raw(
                    f"[{datetime.datetime.now().strftime('%H:%M:%S')}]\n")
            line = prompt_fn(p)
            if self.transcript is not None and not echoes_via_stdout:
                self.transcript.write_input(p, line,
                                            timestamp=self.timestamps and is_main)
            return line
        return fn

    # -- evaluation ----------------------------------------------------------

    def advance_env(self, new_env: int | None, code: str):
        self.env_stack.append(self.cur_env)
        self.cur_env = new_env
        self.history.append(code)

    def drop_from_cache(self, res):
        """Remove an errored command from the crash-recovery session cache."""
        env = getattr(res, "env", None)
        if env is not None and env < 0:
            try:
                self.server.remove_from_session_cache(env)
            except Exception:  # noqa: BLE001
                pass

    def eval_input(self, text: str, allow_incomplete: bool = True) -> str | None:
        """Evaluate one input. Returns "incomplete" when the input parses as an
        unfinished declaration (caller should read continuation lines)."""
        text = text.strip()
        if not text:
            return None
        t0 = time.time()
        status = None
        if first_token(text) == "import":
            mods = [ln.split(None, 1)[1].strip()
                    for ln in text.splitlines() if ln.strip().startswith("import ")]
            self.cmd_import(" ".join(mods))
        elif is_declaration(text):
            res = self.run_cmd(text, env=self.cur_env, cache=True)
            if allow_incomplete and looks_incomplete(res):
                self.drop_from_cache(res)
                return "incomplete"
            errored = self.print_response(res)
            if not errored and not is_error(res):
                self.advance_env(res.env, text)
            else:
                self.drop_from_cache(res)
        else:
            self.eval_expression(text)
        if self.show_time:
            print(dim(f"({time.time() - t0:.2f}s)"))
        return status

    def eval_expression(self, text: str):
        """GHCi-style: try #eval, fall back to #check."""
        res = self.run_cmd(f"#eval ({text})", env=self.cur_env)
        if not is_error(res) and not has_errors(res):
            self.print_response(res)
            return
        res2 = self.run_cmd(f"#check ({text})", env=self.cur_env)
        if not is_error(res2) and not has_errors(res2):
            self.print_response(res2)
            return
        # Neither worked; show the (usually more informative) #eval errors,
        # unless the input failed to parse as a term at all — then run raw.
        res3 = self.run_cmd(text, env=self.cur_env)
        if not is_error(res3) and not has_errors(res3):
            self.print_response(res3)
            self.advance_env(res3.env, text)
            return
        if print_builtin_info(text):
            return
        self.print_response(res)

    # -- commands ------------------------------------------------------------

    def dispatch_command(self, line: str) -> bool:
        """Handle a :command. Returns False if the REPL should exit."""
        parts = line.split(None, 1)
        cmd = parts[0][1:]
        arg = parts[1].strip() if len(parts) > 1 else ""

        if cmd in ("q", "quit", "exit"):
            return False
        elif cmd in ("h", "help", "?"):
            print(HELP)
        elif cmd in ("t", "type"):
            if arg:
                res = self.run_cmd(f"#check ({arg})", env=self.cur_env)
                if (is_error(res) or has_errors(res)) and print_builtin_info(arg):
                    pass
                else:
                    self.print_response(res)
            else:
                print(red("usage: :type EXPR"))
        elif cmd in ("i", "info"):
            if arg:
                res = self.run_cmd(f"#print {arg}", env=self.cur_env)
                if is_error(res) or has_errors(res):
                    # #print only takes identifiers; fall back to #check for
                    # keywords like `Type` and for compound expressions
                    res2 = self.run_cmd(f"#check ({arg})", env=self.cur_env)
                    if not is_error(res2) and not has_errors(res2):
                        self.print_response(res2)
                    elif not print_builtin_info(arg):
                        self.print_response(res)
                else:
                    self.print_response(
                        res, transform=lambda t: format_info(t) or indent_def_body(t))
            else:
                print(red("usage: :info NAME"))
        elif cmd in ("l", "load"):
            self.cmd_load(arg)
        elif cmd in ("r", "reload"):
            if self.loaded_file:
                self.cmd_load(str(self.loaded_file))
            else:
                print(red("no file has been loaded"))
        elif cmd == "import":
            self.cmd_import(arg)
        elif cmd == "imports":
            if self.imports:
                for m in self.imports:
                    print(f"import {m}")
            else:
                print(dim("(no imports)"))
        elif cmd == "browse":
            self.cmd_browse(arg)
        elif cmd == "set":
            if arg:
                res = self.run_cmd(f"set_option {arg}", env=self.cur_env, cache=True)
                if not self.print_response(res) and not is_error(res):
                    self.advance_env(res.env, f"set_option {arg}")
                else:
                    self.drop_from_cache(res)
            else:
                print(red("usage: :set OPTION VALUE"))
        elif cmd == "undo":
            if self.env_stack:
                self.cur_env = self.env_stack.pop()
                if self.history:
                    dropped = self.history.pop()
                    print(dim(f"undid: {dropped.splitlines()[0]}"))
            else:
                print(red("nothing to undo"))
        elif cmd == "reset":
            self.history.clear()
            self.env_stack.clear()
            self.cur_env = self.base_env
            print(dim("session reset" + (" (imports kept)" if self.imports else "")))
        elif cmd == "history":
            if self.history:
                for i, h in enumerate(self.history, 1):
                    first = h.splitlines()[0]
                    more = " …" if "\n" in h else ""
                    print(f"{i:3}  {first}{more}")
            else:
                print(dim("(empty)"))
        elif cmd == "env":
            print(f"environment id: {self.cur_env}")
        elif cmd == "time":
            self.show_time = not self.show_time
            print(dim(f"timing {'on' if self.show_time else 'off'}"))
        elif cmd == "transcript":
            a = arg.strip()
            if not a:
                if self.transcript is not None:
                    print(f"recording to {self.transcript.path}"
                          + (" (with timestamps)" if self.timestamps else ""))
                else:
                    print(dim("transcript is off  (:transcript on|FILE to start)"))
            elif a.lower() == "off":
                self.transcript_stop()
            elif a.lower() == "on":
                self.transcript_start(None)
            else:
                self.transcript_start(a)
        elif cmd == "timestamps":
            a = arg.strip().lower()
            if a in ("on", "true", "1", "yes"):
                self.timestamps = True
            elif a in ("off", "false", "0", "no"):
                self.timestamps = False
            elif not a:
                self.timestamps = not self.timestamps
            else:
                print(red("usage: :timestamps [on|off]"))
                return True
            print(dim(f"per-command timestamps {'on' if self.timestamps else 'off'}"))
        elif cmd == "pickle":
            if arg:
                from lean_interact import PickleEnvironment
                path = str(Path(arg).with_suffix(".olean").resolve())
                res = self.server.run(
                    PickleEnvironment(env=self.cur_env or 0, pickle_to=path),
                    timeout=self.timeout)
                if not self.print_response(res):
                    print(dim(f"environment saved to {path}"))
            else:
                print(red("usage: :pickle FILE"))
        elif cmd == "unpickle":
            if arg:
                from lean_interact import UnpickleEnvironment
                path = str(Path(arg).with_suffix(".olean").resolve())
                res = self.server.run(
                    UnpickleEnvironment(unpickle_env_from=path),
                    timeout=self.timeout)
                if not self.print_response(res) and not is_error(res):
                    self.env_stack.append(self.cur_env)
                    self.cur_env = res.env
                    print(dim(f"environment restored from {path}"))
            else:
                print(red("usage: :unpickle FILE"))
        elif cmd == "!":
            os.system(arg)
        elif cmd == "" and arg == "":
            pass
        else:
            print(red(f"unknown command :{cmd}  (:help for help)"))
        return True

    def cmd_import(self, arg: str):
        mods = [m for m in re.split(r"[,\s]+", arg) if m]
        if not mods:
            print(red("usage: :import MODULE"))
            return
        new = []
        for m in mods:
            if m in self.imports:
                continue
            if not self.module_available(m):
                self.warn_missing_modules([m])
                continue
            new.append(m)
        if not new:
            print(dim("no new modules to import"))
            return
        old_imports = list(self.imports)
        self.imports.extend(new)
        print(dim("Rebuilding session with new imports (this re-elaborates history)..."))
        if not self.rebuild_base_env():
            self.imports = old_imports
            print(red("import failed; session unchanged"))
            self.rebuild_base_env()

    def cmd_load(self, arg: str):
        if not arg:
            print(red("usage: :load FILE"))
            return
        path = Path(arg).expanduser()
        if not path.exists() and not path.suffix:
            path = path.with_suffix(".lean")
        if not path.exists():
            print(red(f"file not found: {path}"))
            return
        text = path.read_text(encoding="utf-8")
        # split leading imports from the body
        body_lines: list[str] = []
        file_imports: list[str] = []
        header_done = False
        for line in text.splitlines():
            s = line.strip()
            if not header_done and s.startswith("import "):
                file_imports.append(s.split(None, 1)[1].strip())
                continue
            if not header_done and (not s or s.startswith("--")):
                continue
            header_done = True
            body_lines.append(line)
        body = "\n".join(body_lines).strip()

        # GHCi-style :load resets the session to the file contents
        self.history.clear()
        self.env_stack.clear()
        for m in file_imports:
            if m not in self.imports:
                self.imports.append(m)
        print(dim(f"Loading {path} ..."))
        t0 = time.time()
        if not self.rebuild_base_env():
            print(red("failed to elaborate imports"))
            return
        if body:
            res = self.run_cmd(body, env=self.base_env, cache=True)
            errored = self.print_response(res)
            if is_error(res):
                return
            self.cur_env = res.env
            if not errored:
                self.history.append(body)
        self.loaded_file = path
        n = len(body.splitlines())
        print(dim(f"Loaded {path.name} ({n} lines) in {time.time() - t0:.1f}s"))

    def cmd_browse(self, arg: str):
        """List session declarations, or declarations in a namespace."""
        if arg:
            code = (
                "open Lean in run_cmd do\n"
                "  let env ← Lean.getEnv\n"
                f"  let pre := `{arg}\n"
                "  let mut names := #[]\n"
                "  for (n, _) in env.constants.toList do\n"
                "    if pre.isPrefixOf n && !n.isInternal then names := names.push n\n"
                "  for n in names.qsort (·.toString < ·.toString) do\n"
                "    Lean.logInfo m!\"{n}\"\n"
            )
            res = self.run_cmd(code, env=self.cur_env)
            if any("include `import Lean" in m.data
                   for m in getattr(res, "messages", []) if m.severity == "error"):
                print(red(":browse needs the Lean metaprogramming API in scope — ")
                      + "run " + bold(":import Lean") + " first")
            elif not getattr(res, "messages", []):
                print(dim(f"(no declarations found under {arg})"))
            else:
                self.print_response(res)
        else:
            if self.history:
                print("\n\n".join(self.history))
            else:
                print(dim("(no session declarations)"))

    # -- main loop -----------------------------------------------------------

    def loop(self):
        if self.args.transcript is not None:
            self.transcript_start(self.args.transcript or None)
        print(cyan(BANNER))
        print(f"LeanRepl — a GHCi-style REPL for Lean 4.  Type {bold(':help')} for help, "
              f"{bold(':quit')} to exit.")
        raw_prompt_fn, echoes = make_prompt_fn()
        prompt_fn = self.wrap_prompt(raw_prompt_fn, echoes)
        if self.args.file:
            self.cmd_load(self.args.file)
        while True:
            try:
                text = self.read_input(prompt_fn)
            except KeyboardInterrupt:
                print(dim("(interrupted — :quit to exit)"))
                continue
            if text is None:
                print(dim("goodbye"))
                break
            stripped = text.strip()
            if not stripped:
                continue
            if stripped.startswith(":") and not stripped.startswith(":="):
                cmd_word = stripped.split(None, 1)[0]
                # ':' commands are REPL commands unless they parse as Lean (e.g. `:= ...` never)
                try:
                    if not self.dispatch_command(stripped):
                        break
                except KeyboardInterrupt:
                    self.handle_interrupt()
                except Exception as e:  # noqa: BLE001
                    self.report_exception(e)
                continue
            try:
                while True:
                    status = self.eval_input(text)
                    if status != "incomplete":
                        break
                    # unfinished declaration: keep reading until a blank line
                    extra = []
                    while True:
                        try:
                            nxt = prompt_fn(self.cont_prompt())
                        except (EOFError, KeyboardInterrupt):
                            break
                        if nxt.strip() == "":
                            break
                        extra.append(nxt)
                    if not extra:
                        self.eval_input(text, allow_incomplete=False)
                        break
                    text = text + "\n" + "\n".join(extra)
            except KeyboardInterrupt:
                self.handle_interrupt()
            except Exception as e:  # noqa: BLE001
                self.report_exception(e)
        if self.transcript is not None:
            self.transcript_stop()

    def report_exception(self, e: Exception):
        if isinstance(e, TimeoutError):
            print(red(f"timeout after {self.timeout}s") +
                  dim(" — the server was restarted; session state is replayed lazily"))
        elif isinstance(e, (ConnectionAbortedError, ConnectionError, BrokenPipeError, EOFError)):
            print(red("the Lean server died: ") + str(e).strip())
            print(yellow("hint: ") + "check that the project is built (`lake build`) and "
                  "that enough memory is available; the session will be restored "
                  "automatically on the next command.")
        else:
            print(red(f"internal error: {e!r}"))

    def handle_interrupt(self):
        print(red("\ninterrupted") +
              dim(" — restarting Lean server (session replays automatically)"))
        try:
            self.server.restart()
        except Exception as e:  # noqa: BLE001
            print(red(f"failed to restart server: {e!r}"))


# ---------------------------------------------------------------------------


def is_error(res) -> bool:
    from lean_interact.interface import LeanError
    return isinstance(res, LeanError)


def looks_incomplete(res) -> bool:
    """True if the only errors are parse errors at end of input, meaning the
    user probably has more lines to type (e.g. `def f : Nat → Nat`)."""
    msgs = [m for m in getattr(res, "messages", []) if m.severity == "error"]
    if not msgs:
        return False
    return all("unexpected end of input" in m.data for m in msgs)


def has_errors(res) -> bool:
    return any(m.severity == "error" for m in getattr(res, "messages", []))


def make_prompt_fn():
    """Return (callable(prompt_str) -> str, echoes_via_stdout).
    echoes_via_stdout is True when the prompt and typed line already pass
    through sys.stdout (so a stdout tee captures them for transcripts)."""
    if not sys.stdin.isatty():
        def fn(p: str) -> str:
            line = input(p)
            print(line)  # echo piped input so transcripts are readable
            return line

        return fn, True
    try:
        from prompt_toolkit import PromptSession
        from prompt_toolkit.history import FileHistory

        histfile = Path.home() / ".leanrepl_history"
        session = PromptSession(history=FileHistory(str(histfile)))

        def fn(p: str) -> str:
            return session.prompt(p)

        return fn, False
    except ImportError:
        def fn(p: str) -> str:
            return input(p)

        return fn, False


def main():
    ap = argparse.ArgumentParser(
        prog="leanrepl",
        description="A GHCi-style interactive REPL for Lean 4.")
    ap.add_argument("file", nargs="?", help="Lean file to load at startup")
    ap.add_argument("--project", "-p", help="path to a Lake project to run inside")
    ap.add_argument("--plain", action="store_true",
                    help="do not use any Lake project (bare Lean + stdlib)")
    ap.add_argument("--lean-version", help="Lean toolchain for --plain mode (e.g. v4.32.0)")
    ap.add_argument("--import", "-i", dest="imports", action="append", metavar="MOD",
                    help="module to import at startup (repeatable, comma-separated ok)")
    ap.add_argument("--timeout", type=float, default=300,
                    help="per-command timeout in seconds (0 = none, default 300)")
    ap.add_argument("--time", action="store_true", help="show per-command timing")
    ap.add_argument("--transcript", nargs="?", const="", default=None, metavar="FILE",
                    help="record a full transcript of the session to FILE "
                         "(default: leanrepl-<date>.log in the current directory)")
    ap.add_argument("--timestamps", action="store_true",
                    help="timestamp each command in the transcript")
    ap.add_argument("--verbose", "-v", action="store_true",
                    help="verbose backend setup output")
    args = ap.parse_args()

    repl = LeanRepl(args)
    try:
        repl.start()
    except KeyboardInterrupt:
        print(red("\nstartup interrupted"))
        return 130
    repl.loop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
