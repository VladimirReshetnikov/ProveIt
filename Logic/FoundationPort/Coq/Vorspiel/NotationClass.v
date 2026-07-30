(** Supplemental logical and coding operation classes.

    These classes deliberately impose no laws: like the source module, they
    only provide a uniform vocabulary that concrete syntaxes may implement. *)

Set Universe Polymorphism.
Set Primitive Projections.

Class lo_tilde (A : Type) := { lo_tilde_op : A -> A }.
Class lo_arrow (A : Type) := { lo_arrow_op : A -> A -> A }.
Class lo_wedge (A : Type) := { lo_wedge_op : A -> A -> A }.
Class lo_vee (A : Type) := { lo_vee_op : A -> A -> A }.
Class lo_box (A : Type) := { lo_box_op : A -> A }.
Class lo_dia (A : Type) := { lo_dia_op : A -> A }.
Class lo_rhd (A : Type) := { lo_rhd_op : A -> A -> A }.
Class lo_tensor (A : Type) := { lo_tensor_op : A -> A -> A }.
Class lo_par (A : Type) := { lo_par_op : A -> A -> A }.
Class lo_with (A : Type) := { lo_with_op : A -> A -> A }.
Class lo_plus (A : Type) := { lo_plus_op : A -> A -> A }.
Class lo_lolli (A : Type) := { lo_lolli_op : A -> A -> A }.
Class lo_bang (A : Type) := { lo_bang_op : A -> A }.
Class lo_quest (A : Type) := { lo_quest_op : A -> A }.
Class lo_exp (A : Type) := { lo_exp_op : A -> A }.
Class lo_smash (A : Type) := { lo_smash_op : A -> A -> A }.
Class lo_length (A : Type) := { lo_length_op : A -> A }.

Class lo_godel_quote (A B : Type) := { lo_quote : A -> B }.

Class lo_sigma_symbol (A : Type) := { lo_sigma : A }.
Class lo_pi_symbol (A : Type) := { lo_pi : A }.
Class lo_delta_symbol (A : Type) := { lo_delta : A }.

Arguments lo_tilde_op {A} {_} _.
Arguments lo_arrow_op {A} {_} _ _.
Arguments lo_wedge_op {A} {_} _ _.
Arguments lo_vee_op {A} {_} _ _.
Arguments lo_box_op {A} {_} _.
Arguments lo_dia_op {A} {_} _.
Arguments lo_rhd_op {A} {_} _ _.
Arguments lo_tensor_op {A} {_} _ _.
Arguments lo_par_op {A} {_} _ _.
Arguments lo_with_op {A} {_} _ _.
Arguments lo_plus_op {A} {_} _ _.
Arguments lo_lolli_op {A} {_} _ _.
Arguments lo_bang_op {A} {_} _.
Arguments lo_quest_op {A} {_} _.
Arguments lo_exp_op {A} {_} _.
Arguments lo_smash_op {A} {_} _ _.
Arguments lo_length_op {A} {_} _.
Arguments lo_quote {A B} {_} _.
Arguments lo_sigma {A} {_}.
Arguments lo_pi {A} {_}.
Arguments lo_delta {A} {_}.
