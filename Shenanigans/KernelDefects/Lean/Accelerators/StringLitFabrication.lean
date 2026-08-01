/-
The kernel FABRICATES an inhabitant of an empty type while expanding a string
literal.  This is a different, and worse, failure mode than the arithmetic
accelerator: no definition of mine "disagrees" with anything -- the kernel simply
builds a term that is not well typed and never checks it.

`src/kernel/inductive.cpp` assembles the term purely from NAMES:

    expr string_lit_to_constructor(expr const & e) {
      string_ref const & s = lit_value(e).get_string();
      std::vector<unsigned> cs;  utf8_decode(s.to_std_string(), cs);
      expr r = *g_list_nil_char;                     -- `List.nil.{0} Char`
      unsigned i = cs.size();
      while (i > 0) { i--;
        r = mk_app(*g_list_cons_char,                -- `List.cons.{0} Char`
                   mk_app(*g_char_of_nat,            -- `Char.ofNat`
                          mk_lit(literal(cs[i]))), r);
      }
      return mk_app(*g_string_mk, r);                -- `String.ofList`
    }

and `inductive_reduce_rec` (src/kernel/inductive.h) feeds it straight to the
recursor rule, with no type check anywhere:

    else if (is_string_lit(major)) major = whnf(string_lit_to_constructor(major));
    optional<recursor_rule> rule = get_rec_rule_for(rec_val, major);
    ...
    rhs = mk_app(rhs, rule->get_nfields(), major_args.data() + nparams);

So `String.rec`'s minor premise is applied to that character list whatever
`String.ofList`'s field type actually is.  Declare the field to be `Empty` --
a type with NO constructors -- and the kernel hands you one.

Needs no `Nat`, no numerals, no `OfNat`, no arithmetic accelerator, and no
`List` or `Char` declarations at all: `List.cons`, `List.nil` and `Char.ofNat`
are never resolved, because the kernel never infers the type of the term it
just built.  A bare string literal is the entire trigger.
-/
prelude

inductive False : Prop

inductive Empty : Type

-- The only way to build a `String` is from an inhabitant of `Empty`.  Nobody
-- can -- except the kernel, when it meets a string literal.
inductive String : Type where
  | ofList : Empty -> String

/-- `Q s` unfolds to `False` for any string the kernel can expand. -/
noncomputable def Q (s : String) : Prop :=
  @String.rec (fun _ => Prop) (fun _ => False) s

/-- Entirely legitimate: `String.ofList` carries an `Empty`, so eliminate it.
    Vacuous in any honest environment. -/
theorem extract (s : String) : Q s :=
  @String.rec (fun s => Q s) (fun e => @Empty.rec (fun _ => False) e) s

/-- The kernel expands `"a"` into
    `String.ofList (List.cons (Char.ofNat 97) List.nil)`, fabricating an
    inhabitant of `Empty`. -/
theorem boom : False := extract "a"

#print axioms boom

theorem anything (P : Prop) : P := @False.rec (fun _ => P) boom

#print axioms anything
