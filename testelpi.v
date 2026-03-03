From elpi Require Import elpi.
Require Import HOL_Light.
Import eqtype choice classical_sets.

Elpi Command Alignment_strategy.

Definition Var {A : Type} := A.
Definition Arg {A : Type} := A.

Elpi Accumulate lp:{{
  % Usage : Alignment_strategy Definition ?stratname
  % (?var1 ?var2 ... : Var)
  % (?field1name : ?field1type)
  % (?field2name : ?field2type) ...
  % (?arg1 ?arg2 ... : Arg) :=
  % (instance1, instance2, ...).
  % States that consecutive fields of type ?field1type ?field2type ... etc
  % can be filled with instance1, instance2 ...
  % But first checks that they are correctly typed [(?instance1 : ?field1type),
  % (?instance2 : ?field2type (?field1name := ?instance1)), etc]

  main [const-decl _ (some Body) _] :- checktyping Body [] Return,
  coq.say Return.
  
  % Checks the instances' types. The second argument is a list remembering all
  % fields (both the variable ?fieldxname and its type fieldxtype)
  func checktyping term, list (pair term term) -> diagnostic.
  func checktyping_phase2 list term, list (pair term term) -> diagnostic.

  checktyping (fun Vname Type RBody) Store Diag :-
    (Type = {{Var}} ; Type = {{Arg}}), !,
    @pi-decl Vname Type x\ checktyping (RBody x) Store Diag.
  
  checktyping (fun Vname Type RBody) Store Diag :- !,
    @pi-decl Vname Type x\ checktyping (RBody x) ((pr x Type) :: Store) Diag.
  
  checktyping Body Store Diag :- !,
    checktyping_phase2 {list_of_tuple Body} {reverse Store} Diag. 
  
  checktyping_phase2 (Term :: _) ((pr _ Type) :: _) (error Msg) :-
    coq.elaborate-skeleton Term Type _ (error Msg), !.

  checktyping_phase2 (Term :: Terms) ((pr X Type)::Store) Diag :- !,
    coq.elaborate-skeleton Term Type NewTerm ok,
    (copy X NewTerm =!=> replace Store NewStore),
    checktyping_phase2 Terms NewStore Diag.
  
  checktyping_phase2 [] [] ok :- !.
  
  func replace list (pair term term) -> list (pair term term).

  replace [] [] :- !.
  replace ((pr X Input) :: Rest1) ((pr X Output) :: Rest2) :- !,
    copy Input Output, replace Rest1 Rest2.
  
  func list_of_tuple term -> list term.

  list_of_tuple (app [global Pair, _, _, TRest, X]) L :-
    coq.locate "pair" Pair, !, rcons {list_of_tuple TRest} X L.
  list_of_tuple T [T] :- !.

  func reverse list A -> list A.

  reverse [] [] :- !.
  reverse (A::L) L' :- !, rcons {reverse L} A L'.

  func rcons list A, A -> list A.

  rcons [] A [A] :- !.
  rcons (A::L) A0 (A::L') :- !, rcons L A0 L'.
}}.

Elpi Alignment_strategy Definition default (T x : Var) (arg1 : T) (arg2 : arg1 = x) := (x, Logic.eq_refl).
Elpi Alignment_strategy Definition default
  (T0 P : Var)
  (T : Type') (mk' : T0 -> T) (dest' : T -> T0)
  (mk_dest' : forall x, mk' (dest' x) = x)
  (dest_mk' : forall x, P x = (dest' (mk' x) = x))
  (x : Arg) (H : @Arg (P x)) :=
  (subtype H, mk H, dest H, mk_dest H, dest_mk H).

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
  pred is_info -> bool.
  %uses coq.info or coq.error depending on first argument
  type infoerror bool -> variadic any (prop).

  gen_name_I Name :- coq.env.fresh-global-id "Unnamed_alignment_instance" Name.

  gen_name_L Name :- coq.env.fresh-global-id "Unnamed_lemma" Name.

  is_info Info? :- attributes A,
    coq.parse-attributes A [att "info" bool] Atts,
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

  pred index -> string.
  index "(o) : open, aligns with command input.".
  index "(d) : default, aligns with a default value when there is one.".

  pred usagemessage -> string.
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

  %In case of no default structure in a context where there should be one.
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

Elpi Command test.
Elpi Accumulate lp:{{
  main [const-decl Name (some Bo) Arity] :-
    coq.say Name Bo Arity.
}}.

Section test.

End test.
Elpi test Definition truc := val.



Elpi test Definition x := .

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