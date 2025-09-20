From elpi Require Import elpi.
Require Import HOL_Light.

Elpi Db align_structures.db lp:{{
  %structure structuretype object objectname
  %declares a structure for that object.
  pred structure o:id o:gref o:id.
  %default_instance objectname instance.
  func default_instance id -> term.
  %auto_instance objectname instance description.
  func auto_instance id -> term, string.
  %generate a name for an instance.
  func gen_name_I -> id.
  %generate a name for a lemma.
  func gen_name_L -> id.
  %the align command, accumulatable.
  pred align_command i:bool, o:list argument.
  %parses attribute #[info]
  func is_info -> bool.
  %uses coq.info or coq.error depending on first argument
  type infoerror bool -> variadic any (func).

  gen_name_I Name :- coq.env.fresh-global-id "Unnamed_alignment_instance" Name.

  gen_name_L Name :- coq.env.fresh-global-id "Unnamed_lemma" Name.

  is_info Info? :- coq.parse-attributes {attributes} [att "info" bool] Atts,
    Atts ==> get-option "info" Info? ; Info? = ff.
  
  infoerror tt A B C D E :- coq.info A B C D E.
  infoerror tt A B C D :- coq.info A B C D.
  infoerror tt A B C :- coq.info A B C.
  infoerror tt A B :- coq.info A B.
  infoerror tt A :- coq.info A.
  infoerror ff A B C D E :- coq.error "Error:" A B C D E.
  infoerror ff A B C D :- coq.error "Error:" A B C D.
  infoerror ff A B C :- coq.error "Error:" A B C.
  infoerror ff A B :- coq.error "Error:" A B.
  infoerror ff A :- coq.error "Error:" A.
}}.

Elpi Command Align.
Elpi Export Align.
Elpi Accumulate Db align_structures.db.

Elpi Accumulate lp:{{
  main Args :- align_command {is_info} Args.
}}.

Elpi Accumulate align_structures.db lp:{{
  align_command tt [] :- std.findall (usagemessage _) Umessages,
    std.findall (index _) Imessages,
    M1 is 
    "Declares an instance for one or multiple alignable structures.\n" ^
    "This command with attribute #[info] prints which structures are\n" ^
    "going to be aligned and in which way, using the following code:",
    coq.info M1,
    std.forall Imessages (infoM index), coq.info
    "-------------------------------------------------------------------------"
    "Align usage:",
    std.forall Umessages (infoM usagemessage).
  
  func infoM (string -> prop), prop.
  infoM Function (Function Message) :- coq.info Message.

  func index -> string.
  index "(o) : open, aligns with command input.".
  index "(d) : default, aligns with a default value when there is one.".

  func usagemessage -> string.
  usagemessage M :- M is
  "Align Name by default -> declares the default instance of the\n" ^
  "  alignable structure Name.".
  usagemessage M :- M is
  "Align Name auto -> declares the automatically deduced instance of the\n" ^
  "  alignable structure Name. Defaults to the default instance\n" ^
  "  if no other instance can be automatically deduced.".

  align_command Info? [str Name, str "by", str "default"] :-
    default_instance Name Obj, !,
    EM is "default instance is ill-formed.\nPlease report this error",
    std.assert-ok! (coq.typecheck Obj T) EM, if (Info? = tt)
      (coq.info "aligns" Name "(d)")
      (coq.env.add-const {gen_name_I} Obj T _ _).
  align_command Info? [str Name, str "by", str "default"] :- !,
    if (structure Struct _ Name)
      (no_default Info? Struct Name)
      (infoerror Info? Name "is not declared as alignable.").

  align_command Info? [str Name, str "auto"] :-
    auto_instance Name Obj Desc, !,
    EM is "auto instance" ^ Desc ^ "is ill-formed.\nPlease report this error",
    std.assert-ok! (coq.typecheck Obj T) EM, if (Info? = tt)
      (coq.info "aligns" Name Desc)
      (coq.env.add-const {gen_name_I} Obj T _ _).
  align_command Info? [str Name, str "auto"] :- !,
    align_command Info? [str Name, str "by", str "default"].

  %customizable error / info message for a structuretype with no default
  %instance. the exact structure Name is only present to be printed.
  func no_default bool, id, id.

  %In case no default structure in a context where there should be one.
  :name "no_default.fail"
  no_default _ _ _ :- coq.error "Error: failed to find a default instance."
  "Please report this.".

  %catch-all rule, should be last. Redirects to command info.
  :name "align.fail"
  align_command _ _ :- !,
    coq.info "Printing command info:",
    align_command tt [], coq.error "Incorrect use of Align.".
}}.

Elpi Command HOL.
Elpi Export HOL.
Elpi Accumulate Db align_structures.db.

Elpi Accumulate lp:{{
  %Shorter way to define a Class.
  func add-record id, id, record-decl.

  add-record Name Structure Record :-
    coq.env.add-indt (record {calc (Name ^ "_Class_HOL")} (sort _)
      {calc (Name ^ "_build_Class_HOL")} Record) R,
    coq.elpi.accumulate _ "align_structures.db"
      (clause _ _ (structure Structure (indt R) Name)).

  %Do like coq.arity->term but transform the term into (Eq Type t1 t2).
  %get_def_type (parameters L Type) t1 t2 = forall L, (eq Type (t1 L) (t2 L)).
  func get_def_type arity, term, term -> term.
  get_def_type (parameter _ _ Ty Rest) T1 (fun Name Ty F) (prod Name Ty R) :-
    @pi-decl Name Ty x\ get_def_type (Rest x) (app [T1, x]) (F x) (R x).
  get_def_type (arity A) T1 T2 TEq :-
    TEq = app [global {coq.locate "eq"}, A, T1, T2].
  
  main [const-decl Name (some Bo) Arity] :-
    Name_def is Name ^ "_def",
    add-record Name "HOL_Definition"
      (field _ Name {coq.arity->term Arity} x\
      field _ Name_def {get_def_type Arity x Bo} y\ end-record),
    coq.arguments.set-implicit {coq.locate Name} [[maximal]],
    coq.arguments.set-implicit {coq.locate Name_def} [[maximal]]. }}.

Elpi Accumulate align_structures.db lp:{{
  %from type forall A B ... N, _ = _, get fun A B ... N => eq_refl _.
  func default_HOL_def_instance_intern term -> term.
  default_HOL_def_instance_intern (prod _ _ Rest) (fun _ _ T) :- !,
    pi x\ default_HOL_def_instance_intern (Rest x) (T x).
  default_HOL_def_instance_intern {{ _ = lp:X }} {{eq_refl lp:X}}.

  %The default instance of a HOL Definition is simply when Name_def is eq_refl.
  default_instance Name Obj :-
    structure "HOL_Definition" _ Name, !,
    coq.locate {calc (Name ^ "_build_Class_HOL")} BuildC,
    Build = global BuildC, coq.typecheck Build (prod _ _ Rest) ok,
    Rest _ = prod _ Type _, default_HOL_def_instance_intern Type EQR,
    EM is "Default instance skeleton failed.\nPlease report this error.",
    std.assert-ok! (coq.elaborate-skeleton (app [Build, _ , EQR]) _ Obj) EM.
}}.

From mathcomp Require Import classical.classical_sets.

Elpi Accumulate align_structures.db lp:{{
  %Store the predicate defining a Type
  func defpred id -> term.
}}.

Elpi Accumulate lp:{{
  func type' term -> term.
  type' T (app [{{Pointed.sort}}, T]).

  main [str "Type", str Name, str Mk, str Dest, str Ax1, str Ax2, str ":=",
  str "subtype", trm Pred] :-
    EM is {coq.term->string Pred} ^ " is not a predicate",
    std.assert (parsepred Pred L Base) EM,
    std.assert-ok! (coq.typecheck Pred (prod _ Base _\{{Prop}})) EM,
    pi typespec\
    coq.elpi.accumulate _ "align_structures.db"
      (clause _ _ (defpred Name Pred)),
    add-record Name "HOL_Type"
      (field _ Name {{Type'}} t\

      field _ Mk {typespec Arglist Base t b\T\prod _ b _\T} mk\ 
      field _ Dest (typespec prod _ {type' t} _\Base) dest\
      field _ Ax1 (prod {coq.id->name "x"} {type' t} x\
      app [{{@Logic.eq (Pointed.sort lp:t)}}, app [mk, app [dest, x]], x]) _\
      field _ Ax2 (prod {coq.id->name "r"} Base r\
      app [{{@Logic.eq Prop}}, app [Pred, r],
      app [{{@Logic.eq}}, Base, app [dest, app [mk, r]], r]]) _\ end-record).
}}.

Elpi Accumulate align_structures.db lp:{{
  :before "no_default.fail"
  no_default Info? "HOL_Type" Name :- !,
    infoerror Info? Name "is a declared HOL Type and thus has no"
    "default instance".
  
  auto_instance Name Instance "(i)" :- defpred Name Pred,
    Pred is 
}}.