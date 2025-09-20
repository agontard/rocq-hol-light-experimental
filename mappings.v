From HOLLight_experimental Require Import HOL_Light theory.
Import classical_sets ssreflect ssrnat ssrfun eqtype choice ssrbool boolp HB.structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(****************************************************************************)
(* To be able to use ext within =>. *)
(****************************************************************************)

(* use /` during ssr intropattern to ext all,
   /f` to only use funext,
   and /n` for n between 1 and 5 ext exactly n arguments / hypotheses. *)

Ltac funext :=
  let rec funext' := (let x := fresh "x" in
    apply funext => x ; try funext' ; move:x)
  in funext'.

Notation "`" := (ltac:(try ext)) (at level 0, only parsing).
Notation "f`" := (ltac:(try funext)) (at level 0, only parsing).

Notation "1`" := (ltac:(first [apply funext | eqProp])) (at level 0, only parsing).

Notation "2`" := (ltac:( let H := fresh in first [apply funext | eqProp]=>H ;
                         first [apply funext | eqProp] ; move: H ))
                           (at level 0, only parsing).

Notation "3`" := (ltac:( let H1 := fresh in first [apply funext | eqProp]=>H1 ;
                         let H2 := fresh in first [apply funext | eqProp]=>H2 ;
                         first [apply funext | eqProp] ; move: H1 H2 ))
                           (at level 0, only parsing).

Notation "4`" := (ltac:( let H1 := fresh in first [apply funext | eqProp]=>H1 ;
                         let H2 := fresh in first [apply funext | eqProp]=>H2 ;
                         let H3 := fresh in first [apply funext | eqProp]=>H3 ;
                         first [apply funext | eqProp] ; move: H1 H2 H3))
                           (at level 0, only parsing).

Notation "5`" := (ltac:( let H1 := fresh in first [apply funext | eqProp]=>H1 ;
                         let H2 := fresh in first [apply funext | eqProp]=>H2 ;
                         let H3 := fresh in first [apply funext | eqProp]=>H3 ;
                         let H4 := fresh in first [apply funext | eqProp]=>H4 ;
                         first [apply funext | eqProp] ; move: H1 H2 H3 H4))
                           (at level 0, only parsing).

(* Definition test (n m k : nat) (f : nat -> nat -> nat) := f = f.
Goal True -> test = test. move => * /f`* /3` H n0 m0. *)

(****************************************************************************)
(* Alignment automation tactics. *)
(****************************************************************************)

(****************************************************************************)
(* For the ε operator *)
(****************************************************************************)

(* The definition of an HOL-Light function that is recursively defined
on some inductive type usually looks like:

  [ε (fun g => forall uv, P (g uv)) uv0]

  where P does not depend on uv (unused variable). *)

(* [gobble f uv] replaces the occurrences of [f uv] by a new symbol
named [f] too and removes [uv] from the context, assuming that [f uv]
does not actually depends on [uv]. *)
Ltac gobble f uv :=
  let g := fresh in
  set (g := f uv) in * ;
  clearbody g ; simpl in g ;
  clear f uv ; rename g into f.

(* From a goal of the form [a = ε (fun a' => forall uv, P (a' uv)) uv0],
align_ε generates two subgoals [P a] and [forall x, P a -> P x -> a = x]. *)
Ltac align_ε :=
  let rec aux :=
    lazymatch goal with
    | |- _ ?x = ε _ ?x => apply (f_equal (fun f => f x)) ; aux
    | |- ?a = ε _ ?r =>
        (* Replace the goal by (fun _ => a = ε ?P) *)
        apply (f_equal (fun g => g r) (x := fun _ => a)) ;
        aux ;
        [ let uv := fresh in
          intro uv ; clear uv 
        | let a' := fresh in
          let uv := fresh in
          let H' := fresh in
          let H := fresh in
          move=> a' H H' /= /1` uv ;
          specialize (H uv) ; (* As [P] starts with [forall uv] *)
          specialize (H' uv) ;
          simpl ((fun _ => a) uv) in * ; (* Simplifies to [a] so that [uv] only appears in [a' uv] *)
          gobble a' uv ;
          revert a' H H' (* Revert [a'], [P a] and [P a'] to reuse them in other tactics *)
        ]
    | |- ?a = ε ?P => apply align_ε (* Replaces the goal [a = ε P] with two goals [P a] and
                                       [forall x, P a => P x => x = a]. *)
    end
  in aux.

(****************************************************************************)
(* For if ... then ... else ... *)
(****************************************************************************)

(* The following are useful tools to work with COND :
   - Tactic if_triv replaces [if P then x else y] in the goal with either x or y
     assuming P or ~P is derivable with easy.
   - Tactic if_intro transforms a goal [P (if Q then x else y)]
     into two goals [Q -> P x] and [~Q -> P y] and
     simplifies all other [if Q then x' else y'] even if x<>x' or y<>y'
   - Lemma if_elim destructs hypothesis [if P then Q else R]
     as if it were (P /\ Q) \/ (~P /\ R) *)

Lemma if_triv_True (A : Type') (P : Prop) (x y : A) : P -> (if P then x else y) = x.
Proof.
  by rewrite -{1}(is_True P) => -> ; exact (if_True _ _).
Qed.

Lemma if_triv_False (A : Type') (P : Prop) (x y : A) : ~P -> (if P then x else y) = y.
Proof.
  by rewrite -{1}(is_False P) => -> ; exact (if_False _ _).
Qed.

Tactic Notation "if_triv" :=
  rewrite/COND ;
  (rewrite if_triv_True ; [auto | easy]) +
  (rewrite if_triv_False ; [auto | easy]).

(* /1= in intropattern *)
Ltac ssrsimpl1 := if_triv.

(* If needed, specify which P is trivial *)
Tactic Notation "if_triv" constr(P) :=
  rewrite/COND ;
  (rewrite (if_triv_True _ P) ; [auto | easy]) +
  (rewrite (if_triv_False _ P) ; [auto | easy]).

Tactic Notation "if_triv using" constr(H) :=
  rewrite/COND ; let H' := fresh in set (H' := H) ;
  (rewrite if_triv_True ; [auto | now auto using H']) +
  (rewrite if_triv_False ; [auto | now auto using H']) ; clear H'.

Tactic Notation "if_triv" constr(P) "using" constr(H) :=
  rewrite/COND ; let H' := fresh in set (H' := H) ;
  (rewrite (if_triv_True _ P) ; [auto | now auto using H']) +
  (rewrite (if_triv_False _ P) ; [auto | now auto using H']) ; clear H'.

Lemma if_intro (A : Type') (Q : Prop) (P : A -> Prop) (x y : A) :
  (Q -> P x) -> (~Q -> P y) -> P (if Q then x else y).
Proof. by case (pselect Q)=>H ; if_triv. Qed.

(* applies if_intro then also clears all if with
   the same hypothesis *)

Ltac if_intro :=
  rewrite/COND ;
  let H := fresh in
  apply if_intro => H ;
  [ repeat rewrite (if_triv_True _ _ H)
  | repeat rewrite (if_triv_False _ _ H)] ;
  move : H.

(* /c` in intropattern, c for case. *)
Notation "c`" := (ltac:(if_intro)) (at level 0, only parsing).

Lemma if_elim (P Q R G : Prop) : (if P then Q else R) -> (P -> Q -> G) -> (~ P -> R -> G) -> G.
Proof.
  by case (pselect P) => H /1=.
Qed.

(****************************************************************************)
(* For partial functions *)
(****************************************************************************)

(* Whenever functions defined in HOL-Light are only defined in some specific cases
   with ε, it can be defined in Rocq with an if then else, to have a meaningful value
   for these specific cases and default to the default ε-chosen function's
   value elsewhere. For example, functions defined on finite sets.

   align_ε_if works similarly to align_ε' in this case, with restraining
   uniqueness to the relevant cases for the function *)

Lemma align_ε_if1 {A B : Type'}
  (Q : A -> Prop) (f : A -> B) (P : (A -> B) -> Prop) :
  P f ->
  (forall f', P f -> P f' -> forall x, Q x -> f x = f' x) ->
  forall x, (if Q x then f x else ε P x) = ε P x.
Proof.
  move=> Hf Hunique x /c` // ; apply Hunique => //.
  by apply ε_spec ; exists f.
Qed.

Lemma align_ε_if2 {A B C : Type'}
  (Q : (A -> B -> Prop)) (f : A -> B -> C) (P : (A -> B -> C) -> Prop) :
  P f ->
  (forall f', P f -> P f' -> forall x y, Q x y -> f x y = f' x y) ->
  forall x y, (if Q x y then f x y else ε P x y) = ε P x y.
Proof.
  move=> Hf Hunique x y /c` // ; apply Hunique => //.
  by apply ε_spec ; exists f.
Qed.

Lemma align_ε_if3 {A B C D : Type'}
  (Q : (A -> B -> C -> Prop)) (f : A -> B -> C -> D) (P : (A -> B -> C -> D) -> Prop) :
  P f ->
  (forall f', P f -> P f' -> forall x y z, Q x y z -> f x y z = f' x y z) ->
  forall x y z, (if Q x y z then f x y z else ε P x y z) = ε P x y z.
Proof.
  move=> Hf Hunique x y z /c` // ; apply Hunique => //.
  by apply ε_spec ; exists f.
Qed.

Arguments align_ε_if1 {_ _} _ _.
Arguments align_ε_if2 {_ _ _} _ _.
Arguments align_ε_if3 {_ _ _ _} _ _.

Ltac align_ε_if :=
  let rec aux :=
    lazymatch goal with
    | |- ?f = ε _ ?uv => generalize uv ; aux ;
          [ intros _
          | let f' := fresh in
            let uv := fresh in
            let Hf := fresh in
            let Hf' := fresh in
            let x := fresh "x" in
            let y := fresh "y" in
            let HP := fresh in
            try intros f' Hf Hf' uv x y HP ; try intros f' Hf Hf' uv x HP ;
            specialize (Hf uv) ;
            specialize (Hf' uv) ;
            simpl (_ uv) in * ;
            gobble f' uv ;
            revert HP ; try revert y ; revert f' Hf Hf' x ]
    | |- _ = ε _ => funext ; (* helping with pattern matching by
                                universally quantifying on the arguments *)
      lazymatch goal with
      | |- forall x, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if1 (fun x => P) (fun x => f))
      | |- forall x y, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if2 (fun x y => P) (fun x y => f))
      | |- forall x y z, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if3 (fun x y z => P) (fun x y z => f)) end
    | |- forall uv, _ = ε _ uv => move=> uv /f` ; revert uv ;
      lazymatch goal with
      | |- forall x, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if1 (fun x => P) (fun x => f))
      | |- forall x y, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if2 (fun x y => P) (fun x y => f))
      | |- forall x y z, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if3 (fun x y z => P) (fun x y z => f)) end end
  in aux.


(****************************************************************************)
(* For inductive propositions. *)
(****************************************************************************)

Ltac breakgoal :=
  match goal with
  | |- _ \/ _ => left + right ; breakgoal (* Try both *)
  | |- exists _,_ => eexists ; breakgoal (* The witness should be obvious *)
  | |- _ => easy end. (* if easy cannot do the job, it fails to branch back. *)

(* simply decomposing each hypothesis that we might encounter,
   a lot faster than going brutally with firstorder *)
Ltac full_destruct := repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists x, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H end.

(* rewrite H but do not fail if H is trivial. Clear it instead. *)
Ltac rewrite' H :=
  let rec check_triv H := idtac ;
    match type of H with
    | forall _, _ => specialize (H point) ; check_triv H
    | ?x = ?x => idtac end
  in tryif check_triv H then clear H else rewrite H /=.

Ltac blindrewrite := repeat match goal with H : _ |- _ => rewrite' H end.

(* Tactic to clear variables not appearing anywhere, including hypotheses. *)

Ltac clearall := repeat match goal with useless : _ |- _ => clear useless end.

(* In HOL_Light, an inductive defintion is top-down :
   if [Case_i x1 ... xn : Hyps_i x1 ... xn -> P (f_i x1 ... xn)] for 1 <= i <= k
   are the constructors / rules of P, then :
   [P x = forall P', (forall x', Case_1' x' \/ ... \/ Case_k' x' -> P' x') -> P' x]
   where [Case_i' x' := exists x1 ... xn, f_i x1 ... xn = x' /\ Hyps_i x1 ... xn]

   Let P_h x := Forall P', H' -> P' x' denote the HOL_Light definition of P
   and P_r the Rocq Inductive definition.
   *)
Ltac ind_align :=
  let H := fresh in
  move => */f`*/1`H ;
  (* Prove equality by double implication *)
  [ let P' := fresh "P'" in
    let H' := fresh "H'" in (* Proving [P_r x -> P_h x] *)
    intros P' H' ; induction H ; apply H' ;
    (* Induction on hypothesis [P_r x] replaces [x] according to Case_i for each i.
       to prove [P' x] we apply [H']. *)
    try breakgoal (* Trying to automatically find and solve Case_i'.
                     The Hyps_i are in the context. *)
  | (* Proving [P_h x -> P_r x] *)
    apply H ; (* Replaces goal [P_r x] with [H'] *)
    clearall ; (* H' talks about fresh variables *)
    intros ; full_destruct ; (* Destructing H results in one goal per case, and separates the hypotheses *)
    blindrewrite ; (* not much to do, each clause should be proved with a rule,
                      we just try to rewrite [a = f x1 ... xn] if it exists *)
    try now (constructor ; auto) ].

(*****************************************************************************)
(* For function inverses *)
(*****************************************************************************)

Definition finv [A B : Type'] (f : A -> B) : B -> A := fun y => ε (fun x => f x = y).

(* finv can define the inverse of a type embedding, the following will be useful to
   prove isomorphisms *)

Lemma finv_inv_l [A B : Type'] (f : A -> B) (x : A) :
  (forall x0 x1 : A, f x0 = f x1 -> x0 = x1) -> finv f (f x) = x.
Proof.
  intro H. apply H. apply (ε_spec (P := fun x' => f x' = f x)). now exists x. 
Qed.

Ltac finv_inv_l := intros ; apply finv_inv_l ; clearall.

Lemma finv_inv_r [A B : Type'] (f : A -> B) : forall (P : B -> Prop) (y : B), 
  (P y -> exists x, f x = y) -> ((exists x, f x = y) -> P y) -> P y = (f (finv f y) = y).
Proof.
  intros P y i1 i2. transitivity (exists x, f x = y).
  - exact (prop_ext i1 i2).
  - move=> /1` H.
    + exact (ε_spec H).
    + now exists (finv f y).
Qed.

(*****************************************************************************)
(* For inductive types *)
(*****************************************************************************)

Require Import Stdlib.NArith.BinNat.

(* This part makes sense after seeing the alignment and explanation of recspace
   somewhere bellow *)

(* In this section, we suppose that we wish to align a HOL_Light inductive definition to a
   Rocq one. In simple cases (Same ammount of constructors with same arguments,
   Rocq generates the correct inductive principle, currently no mutually defined types
   (check coq-hol-light-Logic for an example of alignment of 2 mutually defined types)), the following 
   tactics allow to fully automate the proofs. *)

(* Let this also serve as a tutorial on how to map a HOL Light type T in general.

   - Once file.ml has been translated with hol2dk,
     search for "Axiom" in file_terms.v. You should find axioms,
     usually named _mk_T and _dest_T, with type recspace A -> T and
     T -> recspace A respectively for some A.

   - In the mappings file, first define the correct Rocq inductive type if it does not exist,
     then define _dest_T yourself recursively.
     > To know how you should define it, look at the definitions after axioms _mk_T and _dest_t
       in T_terms.v. They should look like :
       "Definition _123456 := fun (...) => _mk_T [...]" where _123456 (for example) is simply a temporary name
       for a constructor C, replaced soon after with "Definition C := _123456".
       [_dest_T (C (...))] should then have value [...].

    - You can then define _mk_t := finv _dest_t.

    - Then, in file_types.v, you should find two axioms named axiom_... stating
      that _dest_T and _mk_t are the inverse of each other. Prove them in the mappings file using the following
      tactics :
      *)

(* _dest_inj proves that _dest is injective by double induction.
   Can fail when the induction principle isn't suited.
   Only works for non mutually defined types. *)

Ltac _dest_inj_inductive FCONS_inj :=
  match goal with |- forall x x', _ => let e := fresh in
    induction x ; induction x' ; simpl ; intro e ;
    (* e is of the form "CONSTR n a f = CONSTR n' a' f'", so inversion
       gives hypotheses n=n' , a=a' and f=f'. *)
    inversion e ; auto ;
    repeat rewrite -> FCONS_inj in * ; (* f and f' should represent lists of recursive calls
                                       so we transform their equality into equality of
                                       each recursive call (so of the form
                                       "et : _dest_T t = _dest_T t'").
                                       FCONS_inj is a lemma bellow, so we will instantiate
                                       later  *)
    f_equal ;
    match goal with IH : _ |- _ => now apply IH (* trying to apply the
                                                   induction hypothesis blindly to prove 
                                                   t = t' from et *)
    end end.

(* As long as _mk_T is defined as finv _dest_T, _mk_dest_inductive will
   transform a goal of the form [forall x, (_mk_T (_dest_T x)) = x] into
   a goal stating injectivity of _dest_T thanks to finv_inv_l, then try to apply _dest_inj. *)

Ltac _mk_dest_inductive0 FCONS_inj := finv_inv_l ; try _dest_inj_inductive FCONS_inj.

(* Try to solve a goal of the form [forall r, P r = (_dest_T (_mk_T r)) = r)]
   for P defining the subset of recspace A with which the defined type(s) are
   isomorphism.
   Thanks to finv_inv_r, the goal can be replaced by [P r <-> exists x, _dest_T x = r]
   as long as _mk_T is defined as finv _dest_T.

   P is an inductive definition so the following is very similar to ind_align,
   except that [exists x, _dest_T x = r] is not inductive so we are rather inducting on x.
   Compared to ind_align, we do not have access to the constructor tactic to automatically
   find the correct constructor so it currently needs to be done by hand. *)

Ltac _dest_mk_inductive :=
  let H := fresh in 
  let x := fresh "x" in
  intros ; apply finv_inv_r ;
  [ intro H ; apply H ;
    clear H ; intros x H ;
    full_destruct ; rewrite H ;
    clear H ; simpl in *
  | let x := fresh "x" in
    (* simply inducting over [x] such that [_dest_ x = r]. *)
    intros (x,<-) ;
    induction x ; let P := fresh in
    let H' := fresh in
    intros P H' ; apply H' ; try breakgoal ].

(* - Finally, prove the definition of all constructors ( the lemmas _123456_def and C_def
     right under their definition in T_terms.v, replacing them with the new definition ).
     constr_align automatically proves _123456_def (afterwards, C_def is just reflexivity) : *)

Ltac constr_align H := (* Takes as argument the lemma [forall x, f (g x) = x].
                          solves any goal [x = f y] whenever y is computably equal to [g x] *)
  move=> /f`* ; match goal with |- ?x = _ => exact (esym (H x)) end.


(*****************************************************************************)
(* For Record-like types *)
(*****************************************************************************)

(* Record-like types in HOL Light are simply subtypes of the form
   {x : T1 * T2 * ... * Tn | (P1 /\ P2 /\ ... /\ Pn') x}
   where the Pi and Ti are the Prop and non-Prop fields respectively. *)

(* The goal of this section is to automate the alignment of this type
   with the corresponding record in Rocq. *)

(* Note that the Ti cannot depend on each other, since HOL Light cannot define
   dependant pairs. *)

(* let r be an element of the record Type, _dest_T r should simply be the tuple
   of all non-Prop fields of r. We made the choice that _mk_T should be finv _dest_T
   but here other options were available compared to inductive types. *)

(* Revert everything that H does not depend on.
   ( actually also keeps everything that has the same type as H,
     H is supposed to be a proposition ) *)
Ltac revert_keep H :=
  match type of H with ?T =>
    repeat match goal with
    | x : _ |- _ => assert_fails typecheck T x ; revert x end end.

Import ProofIrrelevance.

(* Apply proof_irrelevance to all propositionnal fields,
   to prove injectivity of _dest_T. *)

(* To do that we first need to rewrite equalities to remove the difference in
   dependant typing of the fields. *)

Ltac instance_uniqueness := let instance1 := fresh in
  let instance2 := fresh in
  let eq := fresh in
  intros instance1 instance2 eq ;
  match type of eq with
  | ?f _ = _ => unfold f in eq
  | ?f _ _ = _ => unfold f in eq
  | ?f _ _ _ = _ => unfold f in eq
  | ?f _ _ _ _ = _ => unfold f in eq end ;
  destruct instance1,instance2 ; simpl in eq ;
  revert_keep eq ; inversion_clear eq ;
  intros ; f_equal ; apply proof_irrelevance.

(* Combine it with finv_inv_l. *)

Ltac _mk_dest_record := finv_inv_l ; instance_uniqueness.

(* tries proving [H1 /\ ... /\ Hn -> P] with hypothesis [H1 -> ... -> Hn -> P]
   or the converse. *)

Ltac and_arrow := hnf ; intros ; try match goal with H : _ |- _ => now apply H end.

(* finv_inv_r gives us two goals, we can only fully automate one :
   [exists r' : T, _dest r' = r -> (P1 /\ P2 /\ ... /\ Pn') r]
   which is simply done by rewriting the hypothesis, and destructing r'
   to get its fields which should contain the required proof.  *)

Ltac _dest_mk_record :=
  intros ; apply finv_inv_r ;
  [ try match goal with
    | |- ?P _ -> _ => unfold P
    | |- ?P _ _ -> _ => unfold P
    | |- ?P _ _ _ -> _ => unfold P
    | |- ?P _ _ _ _ -> _ => unfold P end ;
    intros ; full_destruct
  | try match goal with
    | |- (exists _, ?f _ = _) -> _ => unfold f
    | |- (exists _, ?f _ _ = _) -> _ => unfold f
    | |- (exists _, ?f _ _ _ = _) -> _ => unfold f
    | |- (exists _, ?f _ _ _ _  = _) -> _ => unfold f end ; 
    let r := fresh in
    intros [r <-] ; clearall ; destruct r ;
    repeat (and_arrow ; split) ; and_arrow ; simpl ].

(* The other goal is the opposite direction,
   for which it is required to provide an instance of the Rocq record,
   which is sadly not automatable with Rocq alone.
   The following tactic automates everything but require as input
   a uconstr of the form {| F1 := fst r ; ... ; Fn := snd (... (snd r)) |},
   explicitly giving all non-Prop fields.  *)

Ltac destruct_tuple r := let b := fresh in
  destruct r as (?a,b) ; try destruct_tuple b.

Tactic Notation "record_exists" uconstr(uwitness) :=
  unshelve eexists uwitness ;
  and_arrow ;
  try match goal with |- _ = ?r => now try destruct_tuple r end.

(* In case the Prop fields are not the same as the HOL_Light ones,
   we will be left with proving their double implication. *)

(****************************************************************************)
(* For total recursive functions *)
(****************************************************************************)

(* Tries to prove a goal [f = ε P uv] where f is recursively defined. *)
Ltac total_align1 :=
  align_ε ; (* At this state, we have two goals : [P f] and [P f -> P f' -> f = f'].
                We now assume that [P f] is of the form
                [Q1 f C1 = ... /\ Q2 f C2 = ... /\ ... /\ Qn f Cn = ...]
                where the Ci are the constructors of the type and
                the Qi are universal quantifications over other arguments and subterms of the Ci. *)
  [ repeat split ; intros ; auto 
  | let f' := fresh in
    let r := fresh "x" in
    let H := fresh in
    let H' := fresh in
    move=> /= f' H H' /1` r ; induction r => /f`* ;
    try full_destruct ; (* with the correct induction principle, we have one case per clause,
                           we can replace [f] and [f']'s values with the corresponding
                           clause in [P] (that we have split).
                           By also rewriting all induction hypotheses,
                           the goal should become a reflexive equality.

                           For more complex types, it is possible to try and adapt this tactic
                           to specify how the induction hypothesis should be used.
                           See term_align in coq-hol-light-Logic1 for an example 
                           with lists as recursive arguments *)
    repeat match reverse goal with
    H : _ |- _ => rewrite' H end ;
    auto (* reflexivity would be more ideal but sometimes rewriting the induction hypothesis fails
            because the recursive call is dependant on something else, for example something quantified. *)
    ].

(* The following only change which argument induction is applied on. *)

Ltac total_align2 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh "f" in
    let r := fresh "x" in
    let H := fresh in
    let H' := fresh in
    move=> /= f' H H' ; ext 2=> + r ;
    induction r ; let a := fresh "a" in
    move=> a /f`* ;
    try full_destruct ; repeat match reverse goal with
    H : _ |- _ => rewrite' H end ; auto ].

Ltac total_align3 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh "f" in
    let r := fresh "x" in
    let H := fresh in
    let H' := fresh in
    move=> /= f' H H' ; ext 3 => + + r ;
    induction r ; let a := fresh "a" in
    let b := fresh "b" in
    move=> a b /f`* ;
    try full_destruct ; repeat match reverse goal with
    H : _ |- _ => rewrite' H end ; auto ].

Ltac total_align4 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh "f" in
    let r := fresh "x" in
    let H := fresh in
    let H' := fresh in
    move=> /= f' H H' ; ext 4 => + + + r ;
    induction r ; let a := fresh "a" in
    let b := fresh "b" in
    let c := fresh "c" in
    move=> a b c /f`* ;
    try full_destruct ; repeat match reverse goal with
    H : _ |- _ => rewrite' H end ; auto ].

Ltac total_align5 :=
  align_ε ; [ repeat split ; intros ; auto
  | let f' := fresh "f" in
    let r := fresh "x" in
    let H := fresh in
    let H' := fresh in
    intros f' H H' ; ext 5 => + + + + r ;
    induction r ; let a := fresh "a" in
    let b := fresh "b" in
    let c := fresh "c" in
    let d := fresh "d" in
    move=> a b c d /f`* ;
    try full_destruct ; repeat match reverse goal with
    H : _ |- _ => rewrite H' end ; auto ].

Ltac total_align :=
  first
  [ total_align1
  | total_align2
  | total_align3
  | total_align4
  | total_align5 ].

(****************************************************************************)
(* Variant on N. *)
(****************************************************************************)

(* N_rec_alignk for k between 1 and 3 replaces a goal of the form 
     f = ε P uv with two goals PO f and PS f whenever P = PO /\ PS
   totally defines the function by peano recursion on the kth argument. *)
(* These tactics only work for functions with 3 or less arguments. *)

Ltac N_rec_align1 :=
  align_ε ; (* At this state, we have two goals : P f and P f -> P f' -> f = f'.
                We now assume that P is of the form
                g 0 = x /\ forall n, g (Succ n) = y for some x and y. *)
  [ split ; auto (* since it is a conjunction, we can split *)
  | let f' := fresh "f" in
    let n := fresh in
    let HO := fresh in
    let HS := fresh in
    let HO' := fresh in
    let HS' := fresh in
    let IHn := fresh in
    move=> /= f' [HO HS] [HO' HS'] /1` ; unfold eqfun ; (* Naming specifically each clause in H and H'. *)
    match goal with |- forall n, ?P =>
      apply (N.peano_rec (fun n => P)) ; try intros n IHn ; move => /f`* ;
      [ rewrite' HO ; rewrite' HO' (* f 0 and f' 0 are replaced with the same value. This ensures that we are inducting on the correct variable otherwise rewriting would fail. *)
      | rewrite' HS ; rewrite' HS' ; try rewrite <- IHn (* Same as above. *)
      ] ; auto end
        ] .
  (* If all works correctly we have two goals left, PO f and PS f.
     PO f is often already solved, and in easy cases, so is PS f. *) 

(* N_rec_align2 and N_rec_align3 are very similar. *)

Ltac N_rec_align2 :=
  align_ε ; [ split ; auto
  | let f' := fresh "f" in
    let n := fresh in
    let a := fresh "x" in
    let HO := fresh in
    let HS := fresh in
    let HO' := fresh in
    let HS' := fresh in
    let IHn := fresh in
    move=> /= f' [HO HS] [HO' HS'] /2` + n ;
    revert n ; match goal with |- forall n, ?P =>
      apply (N.peano_rec (fun n => P)) ; [
        move=> a /f`* ; rewrite' HO ; rewrite' HO' 
      | move=> n IHn a /f`* ;
        rewrite' HS ; rewrite' HS' ; try rewrite <- IHn ] ; auto end
        ].

Ltac N_rec_align3 :=
  align_ε ; [ split ; auto
  | let f' := fresh "f" in
    let n := fresh in
    let a := fresh "x" in
    let b := fresh "x" in
    let HO := fresh in
    let HS := fresh in
    let HO' := fresh in
    let HS' := fresh in
    let IHn := fresh in
    move=> /= f' [HO HS] [HO' HS'] /3` + + n ; revert n ;
    match goal with |- forall n, ?P =>
      apply (N.peano_rec (fun n => P)) ;
      [ move=> a b /f`* ; rewrite' HO ; rewrite' HO'
      | move=> n IHn a b /f`* ; rewrite' HS ; rewrite' HS' ; try rewrite <- IHn ] ; auto end
        ].

Ltac N_rec_align :=
  first
  [ N_rec_align1
  | N_rec_align2
  | N_rec_align3 ].

(****************************************************************************)
(* For partial recursive functions. *)
(****************************************************************************)

(* It is possible in HOL_Light to define a function
   recursively while not defining it for some constructors.
   The function will then have its value on these constructors chosen
   by the ε operator. In that case it is necessary to define the rocq function
   to be trivially equal to the HOL-Light one on each of these constructors.

   The following tactics allow to align such a partially defined function
   when provided with a predicate Q representing the cases where equality has to
   be trivial.

   Q should be defined inductively so as to be able to automatically discharge
   the goal [Q x -> _=_] via inversion. *)

(* First, the following lemmas mimick align_ε in the case where equality has to
   be trivial on Q. They can be used for any partial function, not just recursive
   (for example, a function defined through "new_specification") *)
Unset Implicit Arguments. 
Lemma partial_align_case1 {U A B : Type'} {uv0 : U} {x : A}
  (Q : A -> Prop) (f : U -> A -> B) (P : (U -> A -> B) -> Prop) :
  P f -> (forall x', Q x' -> f uv0 x' = ε P uv0 x') ->
  (forall f' uv x', P f ->  P f' -> (forall x'', Q x'' -> f uv x'' = f' uv x'') ->
  f uv x' = f' uv x') -> f uv0 x = ε P uv0 x.
Proof.
  intros Hf Htriv Hunique.
  apply Hunique;auto. apply ε_spec. now exists f.
Qed.

Lemma partial_align_case2 {U A B C : Type'} {uv0 : U} {x : B} {y : A}
  (Q : A -> Prop) (f : U -> B -> A -> C) (P : (U -> B -> A -> C) -> Prop) :
  P f -> (forall x' y', Q y' -> f uv0 x' y' = ε P uv0 x' y') ->
  (forall f' uv x' y', P f ->  P f' ->
  (forall x'' y'', Q y'' -> f uv x'' y'' = f' uv x'' y'') ->
  f uv x' y' = f' uv x' y') -> f uv0 x y = ε P uv0 x y.
Proof.
  intros Hf Htriv Hunique.
  apply Hunique;auto. apply ε_spec. now exists f.
Qed.

Lemma partial_align_case3 {U A B C D : Type'} {uv0 : U} {x : B} {y : C} {z : A}
  (Q : A -> Prop) (f : U -> B -> C -> A -> D) (P : (U -> B -> C -> A -> D) -> Prop) :
  P f -> (forall x' y' z', Q z' -> f uv0 x' y' z' = ε P uv0 x' y' z') ->
  (forall f' uv x' y' z', P f ->  P f' ->
  (forall x'' y'' z'', Q z'' -> f uv x'' y'' z'' = f' uv x'' y'' z'') ->
  f uv x' y' z' = f' uv x' y' z') -> f uv0 x y z = ε P uv0 x y z.
Proof.
  intros Hf Htriv Hunique.
  apply Hunique;auto. apply ε_spec. now exists f.
Qed.
Set Implicit Arguments.

(* The following ressembles total_align but also tries to automatically get rid of every cases that
   are in Q. It is designed for recursive functions only. *)
Ltac partial_align1 Q :=
  let f' := fresh "f'" in 
  let uv := fresh "uv" in
  let H := fresh in
  let H' := fresh "H'" in
  let Htriv := fresh "Htriv" in
  match goal with
  |- ?f ?x = ε _ _ ?x => apply (partial_align_case1 Q (fun _ => f)) ; (* replace f with (fun _ => f) uv *)
    clear x ; [repeat split ; auto
    | intro x ; now inversion 1 (* Additional goal
                                   [forall x, Q x -> f uv x = ε uv x] compared to
                                   total_align, if Q is inductive and the equality
                                   is trivial, inversion should do the job. *)
    | move=> f' uv x H H' Htriv /f`* ;
      specialize (H uv) ; specialize (H' uv) ;
      induction x ; try (now apply Htriv ; try constructor ; auto) ; (* automatically takes care of cases
                                                                        in Q. *)
      clear Htriv ; (* We do not want to be able to rewrite Htriv outside of cases in Q. *)
      try full_destruct ;
      repeat match goal with H : _ |- _ => rewrite H end ; auto ] end.

Ltac partial_align2 Q :=
  let f' := fresh "f'" in 
  let uv := fresh "uv" in
  let H := fresh in
  let H' := fresh "H'" in
  let Htriv := fresh "Htriv" in
  match goal with
  |- ?f ?y ?x = ε _ _ ?y ?x => apply (partial_align_case2 Q (fun _ => f)) ;
    clear y x ; [repeat split ; auto
    | intros y x ; now inversion 1
    | move=> f' uv y x H H' Htriv /f`* ;
      specialize (H uv) ; specialize (H' uv) ;
      induction x ; try (now apply Htriv ; try constructor ; auto) ;
      clear Htriv ; try full_destruct ;
      repeat match goal with H : _ |- _ => rewrite H end ; auto ] end.

Ltac partial_align3 Q :=
  let f' := fresh "f'" in 
  let uv := fresh "uv" in
  let H := fresh in
  let H' := fresh "H'" in
  let Htriv := fresh "Htriv" in
  match goal with
  |- ?f ?y ?z ?x = ε _ _ ?y ?z ?x => apply (partial_align_case3 Q (fun _ => f)) ;
    clear y z x ; [repeat split ; auto
    | intros y z x ; now inversion 1
    | move=> f' uv y z x H H' Htriv /f`* ;
      specialize (H uv) ; specialize (H' uv) ;
      induction x ; try (now apply Htriv ; try constructor ; auto) ;
      clear Htriv ; try full_destruct ;
      repeat match goal with H : _ |- _ => rewrite H end ; auto ] end.

Ltac partial_align Q :=
  let x := fresh "x" in
  let y := fresh "y" in
  let z := fresh "z" in
  ext 1 => x ; partial_align1 Q +
  (ext 1 => y ; partial_align2 Q +
  (ext 1 => z ; partial_align3 Q)).


(*****************************************************************************)
(* Alignment of quotients. *)
(*****************************************************************************)

Section Quotient.

  Variables (A : Type') (R : A -> A -> Prop).

  Definition is_eq_class X := exists a, X = R a.

  Definition class_of x := R x.

  Lemma is_eq_class_of x : is_eq_class (class_of x).
  Proof. exists x. reflexivity. Qed.

  Lemma non_empty : is_eq_class (class_of point).
  Proof. exists point. reflexivity. Qed.

  Definition quotient := subtype non_empty.

  Definition mk_quotient : (A -> Prop) -> quotient := mk non_empty.
  Definition dest_quotient : quotient -> (A -> Prop) := dest non_empty.

  Lemma mk_dest_quotient : forall x, mk_quotient (dest_quotient x) = x.
  Proof. exact (mk_dest non_empty). Qed.

  Lemma dest_mk_aux_quotient : forall x, is_eq_class x -> (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk_aux non_empty). Qed.

  Lemma dest_mk_quotient : forall x, is_eq_class x = (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk non_empty). Qed.

  Definition elt_of : quotient -> A := fun x => ε (dest_quotient x).

  Variable R_refl : forall a, R a a.

  Lemma eq_elt_of a : R a (ε (R a)).
  Proof. apply ε_spec. exists a. apply R_refl. Qed.

  Lemma dest_quotient_elt_of x : dest_quotient x (elt_of x).
  Proof.
    unfold elt_of, dest_quotient, dest. destruct x as [c [a h]]; simpl. subst c.
    apply ε_spec. exists a. apply R_refl.
  Qed.

  Variable R_sym : forall x y, R x y -> R y x.
  Variable R_trans : forall x y z, R x y -> R y z -> R x z.

  Lemma dest_quotient_elim x y : dest_quotient x y -> R (elt_of x) y.
  Proof.
    unfold elt_of, dest_quotient, dest. destruct x as [c [a h]]; simpl. subst c.
    intro h. apply R_trans with a. apply R_sym. apply eq_elt_of. exact h.
  Qed.

  Import ProofIrrelevance.

  Lemma eq_class_intro_elt (x y: quotient) : R (elt_of x) (elt_of y) -> x = y.
  Proof.
    destruct x as [c [x h]]. destruct y as [d [y i]]. unfold elt_of. simpl.
    intro r. apply subset_eq_compat. subst c. subst d.
    ext=> a j.

    apply R_trans with (ε (R y)). apply eq_elt_of.
    apply R_trans with (ε (R x)). apply R_sym. apply r.
    apply R_trans with x. apply R_sym. apply eq_elt_of. exact j.

    apply R_trans with (ε (R x)). apply eq_elt_of.
    apply R_trans with (ε (R y)). apply r.
    apply R_trans with y. apply R_sym. apply eq_elt_of. exact j.
  Qed.

  Lemma eq_class_intro (x y: A) : R x y -> R x = R y.
  Proof.
    move=> xy /` a h.
    apply R_trans with x. apply R_sym. exact xy. exact h.
    apply R_trans with y. exact xy. exact h.
  Qed.

  Lemma eq_class_elim (x y: A) : R x = R y -> R x y.
  Proof.
    by move=>->.
  Qed.

  Lemma mk_quotient_elt_of x : mk_quotient (R (elt_of x)) = x.
  Proof.
    apply eq_class_intro_elt. set (a := elt_of x). unfold elt_of.
    rewrite dest_mk_aux_quotient. apply R_sym. apply eq_elt_of.
    exists a. reflexivity.
  Qed.

End Quotient.
Arguments dest_quotient [_] _.
Arguments mk_dest_quotient [_] _.
Arguments dest_mk_aux_quotient [_] _ _ _.

(****************************************************************************)
(* Miscellaneous. *)
(****************************************************************************)

(* Instance diese_i : diese_Class.
Proof. now eexists. Defined. *)

Instance GABS_i : GABS_Class.
Proof. now eexists. Defined.

Canonical GABS_i.

Instance GEQ_i : GEQ_Class.
Proof. now eexists. Defined.

Canonical GEQ_i.

Instance _UNGUARDED_PATTERN_i : _UNGUARDED_PATTERN_Class.
Proof. now eexists. Defined.

Canonical _UNGUARDED_PATTERN_i.

Instance _FALSITY__i : _FALSITY__Class.
Proof. now eexists. Defined.

Canonical _FALSITY__i.

Instance hashek_i : hashek_Class.
Proof. now eexists. Defined.

Canonical hashek_i.

Definition cancel2 (A B : Type) (f : A -> B) (g : B -> A) := cancel g f /\ cancel f g.

Instance ISO_i : ISO_Class.
Proof. by exists cancel2. Defined.

Canonical ISO_i.

(****************************************************************************)
(* Alignment of well-foundedness.
HOL Light: non-empty subsets has minimal, Rocq: has induction *)
(****************************************************************************)

Require Import Corelib.Init.Wf.

Definition well_founded := Corelib.Init.Wf.well_founded.

Instance WF_i : WF_Class.
Proof.
  exists well_founded => A.
  ext => R H.
  - intros X ne.
    destruct ne as [x Hx].
    rewrite <- (notE _); intro goal.
    case (prop_degen (forall y: A, ~ X y)); intro h.
    + rewrite is_True in h.
      assert (~ X x) by exact (h x).
      contradiction.
    + rewrite is_False in h.
      apply h.
      apply (well_founded_induction H).
      intros y g Xy.
      apply goal.
      exists y.
      split; assumption.
  - unfold well_founded.
    case (prop_degen (forall a : A, Acc R a)); intro h.
    + rewrite is_True in h.
      assumption.
    + rewrite -> is_False, <- existsNE in h.
      apply except.
      assert (G: exists x : A, ~ Acc R x /\ (forall y : A, R y x -> ~ ~ Acc R y))
        by apply (H _ h).
      destruct G as [x Gx].
      destruct Gx as [H0 H1].
      apply H0.
      apply Acc_intro.
      intros y Ryx.
      rewrite <- (notE _).
      apply H1.
      assumption.
Defined.

Canonical WF_i.

(****************************************************************************)
(* Alignment of  measures, that is functions A -> N which creates a wf order by inverse image *)
(****************************************************************************)

(* Require Import Stdlib.Arith.PeanoNat.

Lemma inj_lt m n: (N.to_nat m > N.to_nat n)%coq_nat = (n < m)%N.
Proof.
  ext => h.
  - unfold N.lt.
    rewrite (Nnat.N2Nat.inj_compare n m).
    apply (proj2 (Nat.compare_lt_iff _ _)).
    assumption.
  - apply (proj1 (Nat.compare_lt_iff _ _)).
    rewrite <- (Nnat.N2Nat.inj_compare n m).
    unfold N.lt in h.
    assumption.
Qed.

Definition MEASURE {A : Type'} : (A -> N) -> A -> A -> Prop := fun f : A -> N => @Wf_nat.gtof A (fun x : A => N.to_nat (f x)).

Lemma MEASURE_def {A : Type'} : (fun f : A -> N => @Wf_nat.gtof A (fun x : A => N.to_nat (f x))) = (fun _8094 : A -> N => fun x : A => fun y : A => N.lt (_8094 x) (_8094 y)).
Proof.
  apply fun_ext; intro f.
  unfold Wf_nat.gtof, MEASURE.
  ext x y.
  exact (inj_lt _ _).
Defined.*)

(****************************************************************************)
(* Some objects used to define integers. *)
(****************************************************************************)

Definition IND_SUC_pred := fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).

Instance IND_SUC_i : IND_SUC_Class.
Proof. now eexists. Defined.

Canonical IND_SUC_i.

Lemma IND_SUC_prop : IND_SUC_pred IND_SUC.
Proof. apply ε_spec. apply thm_IND_SUC_0_EXISTS. Qed.

Lemma IND_SUC_inj : ONE_ONE IND_SUC.
Proof.
  by move=> ? ? ; destruct IND_SUC_prop as [_ [-> _]].
Qed.

Definition IND_0_pred := fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)).

Instance IND_0_i : IND_0_Class.
Proof. now eexists. Defined.

Canonical IND_0_i.

Lemma IND_0_prop : IND_0_pred IND_0.
Proof. apply ε_spec. apply IND_SUC_prop. Qed.

Lemma IND_SUC_neq_0 i : IND_SUC i <> IND_0.
Proof. apply IND_0_prop. Qed.

Inductive NUM_REPi : ind -> Prop :=
  | NUM_REP_0 : NUM_REPi IND_0
  | NUM_REP_S i : NUM_REPi i -> NUM_REPi (IND_SUC i).

Instance NUM_REP_i : NUM_REP_Class.
Proof. exists NUM_REPi ; ind_align. Defined.

Canonical NUM_REP_i.

(****************************************************************************)
(* Alignment(s) of the type of natural numbers. *)
(****************************************************************************)
(* 
Fixpoint dest_num_nat n :=
  match n with
  |0 => IND_0
  |S n => IND_SUC (dest_num_nat n) end.

Definition mk_num_nat := finv dest_num_nat.

Lemma axiom_7_nat : forall (a : nat), (mk_num_nat (dest_num_nat a)) = a.
Proof.
  move=> n ; apply finv_inv_l => {n}.
  elim => /= [|n IHn] ; elim => /= [|m IHm] ; first by [].
  rewrite (sym IND_0).
  1,2 : move=>discr ; destruct (IND_SUC_neq_0 discr).
  by move=> /IND_SUC_inj/IHn->.
Qed.

Lemma axiom_8_nat : forall (r : ind), (NUM_REP r) = ((dest_num_nat (mk_num_nat r)) = r).
Proof.
  move=> r ; apply finv_inv_r.
  - elim => [|i _ [m <-]] ; first by exists 0.
    by exists (S m).
  - by move=> [m <-] ; elim: m ; constructor.
Qed.

Instance nat_num : num_Class := {|
  axiom_7 := axiom_7_nat ;
  axiom_8 := axiom_8_nat |}.

Canonical nat_num.

Lemma _0_def_nat : 0 = (mk_num IND_0).
Proof.
  constr_align axiom_7.
Qed.

Instance nat__0 : _0_Class := {|
  _0_def := _0_def_nat |}.

Canonical nat__0.

Lemma SUC_def_nat : S = (fun _2104 : num => mk_num (IND_SUC (dest_num _2104))).
Proof.
  constr_align axiom_7.
Qed.

Instance nat_SUC : SUC_Class := {|
  SUC_def := SUC_def_nat |}.

Canonical nat_SUC.

Lemma NUMERAL_def_nat : @id nat = (fun _2128 : num => _2128).
Proof. reflexivity. Qed.

Instance nat_NUMERAL : NUMERAL_Class := {|
  NUMERAL_def := NUMERAL_def_nat |}.

Canonical nat_NUMERAL.

Lemma BIT0_def_nat : Nat.double = @ε (arr num num) (fun y0 : num -> num => ((y0 (NUMERAL _0)) = (NUMERAL _0)) /\ (forall y1 : num, (y0 (SUC y1)) = (SUC (SUC (y0 y1))))).
Proof.
  total_align. simpl. lia.
Qed.

Instance nat_BIT0 : BIT0_Class := {|
  BIT0_def := BIT0_def_nat |}.

Canonical nat_BIT0.

Definition Sdouble n := S (BIT0 n).

Lemma BIT1_def_nat : Sdouble = (fun _2143 : num => SUC (BIT0 _2143)).
Proof. reflexivity. Qed.

Instance nat_BIT1 : BIT1_Class := {|
  BIT1_def := BIT1_def_nat |}.

Canonical nat_BIT1.

Lemma add_def_nat : Nat.add = (@ε (arr num (arr num (arr num num))) (fun add' : num -> num -> num -> num => forall _2155 : num, (forall n : num, (add' _2155 (NUMERAL _0) n) = n) /\ (forall m : num, forall n : num, (add' _2155 (SUC m) n) = (SUC (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))).
Proof.
  total_align.
Qed.

Instance nat_add : add_Class := {|
  add_def := add_def_nat |}.

Canonical nat_add.

Open Scope N_scope. *)

(* Not using is_Type' to keep its boolean equality *)

From Stdlib Require Import NArith.BinNat micromega.Lia.
Open Scope N_scope.
HB.instance Definition _ := gen_choiceMixin N.

HB.instance Definition _ := isPointed.Build _ 0.

Lemma N0_or_succ n : n = 0 \/ exists p, n = N.succ p.
Proof. case:(pselect (n=0))=>H. auto. right. exists (N.pred n). lia. Qed.

Lemma recursion_succ A (a:A) f n :
  N.recursion a f (N.succ n) = f n (N.recursion a f n).
Proof.
  apply N.recursion_succ. reflexivity.
  intros n1 n2 n12 a1 a2 a12. subst n2. subst a2. reflexivity.
Qed.

Definition dest_num_N := N.recursion IND_0 (fun _ r => IND_SUC r).

Lemma dest_num0 : dest_num_N 0 = IND_0.
Proof. unfold dest_num. apply N.recursion_0. Qed.

Lemma dest_numS n : dest_num_N (N.succ n) = IND_SUC (dest_num_N n).
Proof. unfold dest_num_N at 1. apply recursion_succ. Qed.

Lemma dest_num_inj : injective dest_num_N.
Proof.
  intro x. pattern x. revert x. apply N.peano_ind.
  intro y. destruct (N0_or_succ y) as [h|[p h]]; subst y. reflexivity.
  rewrite dest_numS.
intro e. apply False_ind. eapply IND_SUC_neq_0. symmetry. exact e.
  intros x hx y. destruct (N0_or_succ y) as [h|[p h]]; subst y.
  rewrite dest_numS.
  intro e. apply False_ind. eapply IND_SUC_neq_0. exact e.
  rewrite !dest_numS. intro e. apply (f_equal N.succ). apply hx.
  apply IND_SUC_inj. exact e.
Qed.

Definition dest_num_img i := exists n, i = dest_num_N n.

Lemma NUM_REP_eq_dest_num_img : NUM_REP = dest_num_img.
Proof.
  ext=> n ; first elim => [|_ _ [m ->]] ; first by exists 0.
  - by exists (N.succ m) ; rewrite dest_numS.
  - move=> [m ->] ; move: m ; apply N.peano_ind.
    + rewrite dest_num0 ; exact NUM_REP_0.
    + move=>m Hm ; rewrite dest_numS ; exact (NUM_REP_S Hm).
Qed.

Lemma NUM_REP_dest_num k : NUM_REP (dest_num_N k).
Proof. rewrite NUM_REP_eq_dest_num_img. exists k. reflexivity. Qed.

Definition mk_num_pred i n := i = dest_num_N n.

Definition mk_num_N i := ε (mk_num_pred i).

Lemma mk_num_ex i : NUM_REP i -> exists n, mk_num_pred i n.
Proof.
  induction 1.
  exists 0. reflexivity.
  destruct IHNUM_REPi as [n hn]. exists (N.succ n). unfold mk_num_pred.
  rewrite hn dest_numS. reflexivity.
Qed.

Lemma mk_num_prop i : NUM_REP i -> dest_num_N (mk_num_N i) = i.
Proof. intro hi. symmetry. apply (ε_spec (mk_num_ex hi)). Qed.

Notation dest_num_mk_num := mk_num_prop.

Lemma mk_num_dest_num k : mk_num_N (dest_num_N k) = k.
Proof. apply dest_num_inj. apply dest_num_mk_num. apply NUM_REP_dest_num. Qed.

Lemma axiom_7_N : forall (a : N), (mk_num_N (dest_num_N a)) = a.
Proof. exact mk_num_dest_num. Qed.

Lemma axiom_8_N : forall (r : ind), (NUM_REP r) = ((dest_num_N (mk_num_N r)) = r).
Proof.
  move=> r /`. apply dest_num_mk_num. intro h. rewrite <- h.
  apply NUM_REP_dest_num.
Qed.

Instance N_num : num_Class := {|
  axiom_7 := axiom_7_N ;
  axiom_8 := axiom_8_N |}.

Canonical N_num.

Lemma _0_def_N : 0 = (mk_num IND_0).
Proof. constr_align axiom_7. Qed.

Instance N__0 : _0_Class := {|
  _0_def := _0_def_N |}.

Canonical N__0.

Lemma mk_num_S : forall i, NUM_REP i -> mk_num_N (IND_SUC i) = N.succ (mk_num_N i).
Proof.
  intros i hi. rewrite NUM_REP_eq_dest_num_img in hi. destruct hi as [n hn].
  subst i. rewrite mk_num_dest_num -dest_numS mk_num_dest_num. reflexivity.
Qed.

Lemma SUC_def_N : N.succ = (fun _2104 : N => mk_num_N (IND_SUC (dest_num_N _2104))).
Proof.
  symmetry. ext=>x. rewrite mk_num_S. 2: apply NUM_REP_dest_num.
  apply f_equal. apply axiom_7_N.
Qed.

Instance N_SUC : SUC_Class := {|
  SUC_def := SUC_def_N |}.

Canonical N_SUC.

(****************************************************************************)
(* Alignment of mathematical functions on natural numbers with N. *)
(****************************************************************************)

(* simpl to replace HOL_Light names with their N instance so that the tactic
   can recognize them. Also unfold mathcomp definitions. *)
Ltac lia := simpl ; unfold addn,muln ; Lia.lia.

Instance N_NUMERAL : NUMERAL_Class.
Proof. now eexists. Defined.

Canonical N_NUMERAL.

Lemma BIT0_def_N : N.double = @ε (arr num num) (fun y0 : num -> num => ((y0 (NUMERAL _0)) = (NUMERAL _0)) /\ (forall y1 : num, (y0 (SUC y1)) = (SUC (SUC (y0 y1))))).
Proof. N_rec_align1. lia. Qed.

Instance N_BIT0 : BIT0_Class := {|
  BIT0_def := BIT0_def_N |}.

Canonical N_BIT0.

Lemma BIT1_def_N : N.succ_double = (fun _2143 : N => SUC (BIT0 _2143)).
Proof. by ext ; elim. Qed.

Instance N_BIT1 : BIT1_Class := {|
  BIT1_def := BIT1_def_N |}.

Canonical N_BIT1.

Lemma add_def_N : N.add = (@ε (arr num (arr num (arr num num))) (fun add' : num -> num -> num -> num => forall _2155 : num, (forall n : num, (add' _2155 (NUMERAL _0) n) = n) /\ (forall m : num, forall n : num, (add' _2155 (SUC m) n) = (SUC (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))).
Proof.
  N_rec_align1. simpl. lia.
Qed.

Instance N_add : add_Class := {|
  add_def := add_def_N |}.

Canonical N_add.

Instance N_PRE : PRE_Class.
Proof.
  exists N.pred. N_rec_align. lia.
Defined.

Canonical N_PRE.

Instance N_mul : mul_Class.
Proof.
  exists N.mul. N_rec_align. lia.
Defined.

Canonical N_mul.

Instance N_EXP : EXP_Class.
Proof.
  exists N.pow. N_rec_align. exact N.pow_succ_r'.
Defined.

Canonical N_EXP.

Instance N_le : le_Class.
Proof.
  exists N.le. N_rec_align.
  - move=> n. apply propext.
    exact (N.le_0_r n).
  - intros n m.
    apply propext.
    rewrite or_comm.
    exact (N.le_succ_r n m).
Defined.

Canonical N_le.

Instance N_lt : lt_Class.
Proof.
  exists N.lt. N_rec_align.
  - intro n.
    rewrite is_False.
    exact (N.nlt_0_r n).
  - intros n m.
    apply propext.
    rewrite N.lt_succ_r.
    rewrite or_comm.
    exact (N.lt_eq_cases n m).
Defined.

Canonical N_lt.

Instance N_ge : ge_Class.
Proof. exists N.ge. ext;lia. Defined.

Canonical N_ge.

Instance N_gt : gt_Class.
Proof. exists N.gt. ext;lia. Defined.

Canonical N_gt.

Instance N_MAX : MAX_Class.
Proof.
  exists N.max => /` x y /c` ; lia.
Defined.

Canonical N_MAX.

Instance N_MIN : MIN_Class.
Proof.
  exists N.min => /` x y /c` ; lia.
Defined.

Canonical N_MIN.

Instance N_minus : minus_Class.
Proof.
  exists N.sub. N_rec_align.
  - exact N.sub_0_r.
  - exact N.sub_succ_r.
Defined.

Canonical N_minus.

(* (n+k)!/k! = (k+1) * (k+1) * ... * (k+n) : product of sequence.
   Easier to define on N than factorial alone. *)

Fixpoint prod_seq_pos p k := match p with
  | xH => N.succ k
  | xO p => prod_seq_pos p k * (prod_seq_pos p ((N.pos p) + k))
  | xI p => (prod_seq_pos p k) *
            (prod_seq_pos p ((N.pos p)+k)) * (k + N.succ_double (N.pos p)) end.

Definition prod_seq n k := match n with
  | 0 => 1
  | N.pos p => prod_seq_pos p k end.

(* Same on nat, easier to reason with. *)

Close Scope N_scope.

Fixpoint prod_seq_nat n k := match n with
  | 0 => 1
  | S n => prod_seq_nat n k * (k + S n) end.

Lemma prod_seq_nat_Sn_m : forall n k,
  prod_seq_nat n.+1 k = prod_seq_nat n k * (k + S n).
Proof. reflexivity. Qed.

Lemma prod_seq_nat_n_Sm : forall n k,
  k.+1 * prod_seq_nat n k.+1 = prod_seq_nat n.+1 k.
Proof.
  induction n => k ; first by rewrite /= mulnC addn1.
  by simpl ; rewrite mulnA IHn addSn -addnS.
Qed.

(* To rewrite a view. *)
Notation "H **" := (reflect_eq H).

Lemma strictly_increasing_inj f :
  (forall n m, n < m -> f n < f m) ->
  forall n m, f n = f m -> n = m.
Proof.
  move=>fsi n m Hnm ; rewrite eqP** eqn_leq -andP**. 
  by split ; generalize Logic.I ; apply contraPleq => temp _ ;
  move : {temp} (fsi _ _ temp) ; rewrite ltn_neqAle Hnm eq_refl.
Qed.

Lemma mulSn_inj k n m : S k * n = S k * m -> n = m.
Proof.
  by apply strictly_increasing_inj => * ; rewrite ltn_pmul2l.
Qed.

Lemma telescope_prod_seq_nat : forall a b c,
  prod_seq_nat (a+b) c = prod_seq_nat b c * (prod_seq_nat a (b+c)).
Proof.
  move=> a b ; move:a ; induction b => a c ; first by rewrite mul1n add0n addn0.
  destruct c ; first by rewrite addnS -2!prod_seq_nat_n_Sm 2!mul1n addSn -addnS.
  apply (@mulSn_inj c) ; rewrite mulnA 2! prod_seq_nat_n_Sm /= addnS -addSn IHb.
  rewrite -?mulnA ?addSn ?addnS (addnC b) 2!prod_seq_nat_n_Sm /= -?mulnA.
  do 2 f_equal ; lia.
Qed.

Import Nnat Nat2N.
Ltac to_nat := autorewrite with Nnat ; fold addn ; fold muln.

Lemma prod_seq_N_nat : forall n k,
  prod_seq n k = N.of_nat (prod_seq_nat (N.to_nat n) (N.to_nat k)).
Proof.
  destruct n ; first by reflexivity.
  simpl prod_seq ; induction p ; simpl prod_seq_pos => k.
  - fold (N.succ_double (N.pos p)) ; to_nat.
    rewrite prod_seq_nat_Sn_m mul2n -{1}addnn telescope_prod_seq_nat.
    simpl prod_seq_pos ; rewrite 2!inj_mul ; do 2 f_equal.
    + exact (IHp _).
    + by rewrite IHp ; do 2 f_equal ; fold (N.pos p + k)%N ;to_nat.
    + rewrite inj_add inj_succ -mul2n inj_double.
      to_nat ; generalize (N.pos p) ; lia.
  - fold (N.double (N.pos p)) ; to_nat.
    rewrite mul2n -{1}addnn telescope_prod_seq_nat.
    rewrite inj_mul ; f_equal.
    + exact (IHp _).
    + by rewrite IHp ; do 2 f_equal ; fold (N.pos p + k)%N ;to_nat.
  - by rewrite /= mul1n addn1 inj_succ ; to_nat.
Qed.

Open Scope N_scope.

Definition fact n := prod_seq n 0.

Instance N_FACT : FACT_Class.
Proof.
  exists fact. N_rec_align.
  intro n. rewrite/fact prod_seq_N_nat /=.
  to_nat. rewrite /= inj_mul -N2Nat.inj_0 -prod_seq_N_nat N.mul_comm ; f_equal.
  by rewrite inj_add inj_succ ; to_nat.
Defined.

Canonical N_FACT.

Lemma Nswap_add_sub a a' b : a' <= a -> a + b - a' = a - a' + b.
Proof. lia. Qed.

Lemma Ndivmod_unicity k k' r r' q :
  r < q -> r' < q -> k * q + r = k' * q + r' -> k = k' /\ r = r'.
Proof.
  intros h h' e.
  assert (e2 : k * q + r - k' * q = k' * q + r' - k' * q). lia.
  case:(pselect (N.lt k k'))=>H. nia.
  rewrite -> thm_ADD_SUB2, Nswap_add_sub, <- N.mul_sub_distr_r in e2 ; nia.
Qed.

Arguments Ndivmod_unicity [_] [_] [_] [_] _.

Instance N_DIV : DIV_Class.
Proof.
  exists N.div. simpl.
  align_ε.
  - exists N.modulo=> m n /c` h.
    + rewrite h.
      split.
      * exact (N.div_0_r m).
      * exact (N.mod_0_r m).
    + split.
      * rewrite N.mul_comm.
        exact (N.Div0.div_mod m n).
      * exact (N.mod_lt m n h).
  - move=> div' _ [mod' h] /` x y.
    apply (if_elim (h x y)) => c [d m].
    + rewrite d c.
      exact (N.div_0_r x).
    + apply (@proj1 _ (x mod y = mod' x y)).
      apply (Ndivmod_unicity y).
      * exact (N.mod_lt x y c).
      * exact m.
      * rewrite <- d, N.mul_comm.
        exact (esym (N.Div0.div_mod x y)).
Defined.

Canonical N_DIV.

Instance N_MOD : MOD_Class.
Proof.
  exists N.modulo. simpl.
  align_ε.
  - move=> m n /c` [->|h] ; split.
    + exact (N.div_0_r m).
    + exact (N.mod_0_r m).
    + rewrite N.mul_comm.
      exact (N.Div0.div_mod m n).
    + exact (N.mod_lt m n h).
  - move=> mod' _ h /` x y.
    apply (if_elim (h x y)) => c [d m].
    + rewrite m c.
      exact (N.mod_0_r x).
    + apply (@proj2 (x / y = x / y)).
      apply (Ndivmod_unicity y).
      * exact (N.mod_lt x y c).
      * exact m.
      * rewrite -d N.mul_comm.
        exact (esym (N.Div0.div_mod x y)).
Defined.


(****************************************************************************)
(* Alignment of the Even and Odd predicates. *)
(****************************************************************************)

Instance N_EVEN : EVEN_Class.
Proof.
  exists N.even. N_rec_align.
  - by rewrite is_True.
  - by move=>n ; rewrite negP** N.even_succ.
Defined.

Canonical N_EVEN.

Instance N_ODD : ODD_Class.
Proof.
  exists N.odd. N_rec_align.
  - by rewrite is_False.
  - by move=>n ; rewrite negP** negPn** N.odd_succ.
Defined.

Canonical N_ODD.

(****************************************************************************)
(* Embeddings used in the definition of recspace. *)
(****************************************************************************)

(* Refer to hol-light/ind_types.ml for explanations *)

Instance N_NUMPAIR : NUMPAIR_Class.
Proof. by eexists. Defined.

Canonical N_NUMPAIR.

Instance N_NUMFST : NUMFST_Class.
Proof. by eexists. Defined.

Canonical N_NUMFST.

Instance N_NUMSND : NUMSND_Class.
Proof. by eexists. Defined.

Canonical N_NUMSND.

Instance N_NUMSUM : NUMSUM_Class.
Proof. by eexists. Defined.

Canonical N_NUMSUM.

Definition NNUMLEFT n := if N.even n then False else True.

Definition NNUMRIGHT n := if N.even n then n / 2 else (n - 1) / 2.

Lemma NUMLEFT_NUMRIGHT_spec P n :
  NNUMLEFT (NUMSUM P n) = P /\ NNUMRIGHT (NUMSUM P n) = n.
Proof.
  unfold NNUMLEFT,NNUMRIGHT. destruct n.
  - move=> /= /c` ; split => //=.
    by is_True H. by is_False H.
  - simpl. rewrite -2!N.div2_div => /c` /= H.
    by is_True H. by is_False H.
Qed.

Lemma NUMSUM_surjective n : exists P m, n = NUMSUM P m.
Proof.
  exists (NNUMLEFT n). exists (NNUMRIGHT n).
  rewrite/NNUMLEFT/NNUMRIGHT /=.
  case_eq (N.even n) => h /1=.
  - rewrite N.even_spec in h. destruct h as [k ->].
    by rewrite thm_DIV_MULT.
  - apply negbT in h. fold (N.odd n) in h.
    rewrite/is_true N.odd_spec in h. destruct h as [k ->].
    by rewrite N.add_sub N.add_1_r thm_DIV_MULT.
Qed.

Instance N_NUMLEFT : NUMLEFT_Class.
Proof.
  exists NNUMLEFT. align_ε.
  - exists NNUMRIGHT.
    exact NUMLEFT_NUMRIGHT_spec.
  - move => NUMLEFT' [? H] [NUMRIGHT' H'] /1` n.
    destruct (NUMSUM_surjective n) as [P [m ->]].
    by rewrite (proj1 (H' P m)) ; apply H.
Defined.

Canonical N_NUMLEFT.

Instance N_NUMRIGHT : NUMRIGHT_Class.
Proof.
  exists NNUMRIGHT. align_ε.
  - exact NUMLEFT_NUMRIGHT_spec.
  - move => NUMRIGHT' H H' /1` n. destruct (NUMSUM_surjective n) as [P [m ->]].
    by rewrite (proj2 (H' P m)) ; apply H.
Defined.

Canonical N_NUMRIGHT.

(****************************************************************************)
(* Alignment of recspace, the HOL-Light type used to encode inductive types. *)
(****************************************************************************)

(* recspace is basically an inductive type with one constant constructor BOTTOM
   and one recursive constructor CONSTR : N -> A -> (N -> recspace A) -> recspace A,
   defined through an embedding inside M := N -> A -> Prop.
   INJN, INJA and INJF embed N, A and N -> M inside M,
   which, together with INJP embedding M*M inside M, allows to embed 
   N * A * (N -> M). *)

Instance N_INJN : INJN_Class.
Proof. by eexists. Defined.

Canonical N_INJN.

Instance N_INJA : INJA_Class.
Proof. by eexists. Defined.

Canonical N_INJA.

Instance N_INJF : INJF_Class.
Proof. by eexists. Defined.

Canonical N_INJF.

Instance N_INJP : INJP_Class.
Proof. by eexists. Defined.

Canonical N_INJP.

Instance N_ZCONSTR : ZCONSTR_Class.
Proof. by eexists. Defined.

Canonical N_ZCONSTR.

Arguments ZCONSTR : simpl never.

Instance N_ZBOT : ZBOT_Class.
Proof. by eexists. Defined.

Canonical N_ZBOT.

Arguments ZBOT : simpl never.

Inductive ZRECSPACEi {A : Type'} : (N -> A -> Prop) -> Prop :=
| ZRECSPACE0 : ZRECSPACEi (ZBOT A)
| ZRECSPACE1 c i r : (forall n, ZRECSPACEi (r n)) -> ZRECSPACEi (ZCONSTR A c i r).

Lemma ZRECSPACEi_def : forall A : pointedType, @ZRECSPACEi A = (fun a : num -> A -> Prop => forall ZRECSPACE' : (num -> A -> Prop) -> Prop, (forall a' : num -> A -> Prop, a' = ZBOT A \/ (exists (c : num) (i : A) (r : num -> num -> A -> Prop), a' = ZCONSTR A c i r /\ (forall n : num, ZRECSPACE' (r n))) -> ZRECSPACE' a') -> ZRECSPACE' a).
Proof. ind_align. Qed.

Instance N_ZRECSPACE : ZRECSPACE_Class := {| ZRECSPACE_def := ZRECSPACEi_def |}.

Canonical N_ZRECSPACE.

Inductive Nrecspace (A : Type) :=
| NBOTTOM : Nrecspace A
| NCONSTR : N -> A -> (N -> Nrecspace A) -> Nrecspace A.

Arguments NCONSTR [A] _ _ _.
Arguments NBOTTOM {A}.

HB.instance Definition _ A := is_Type' (@NBOTTOM A).

(* Explanations. *)

(* Suppose you wish to mutually define inductive types B1 ... Bn.

   - A is the product of the types of all external arguments in constructors of B1 ... Bn.
     ( Without waste, if two constructors use an argument of the same type, it won't appear twice in A. )
     ( Any argument not appearing in a constructor will be replaced by (ε (fun => True)). )
     ( If no constructor has external arguments then A is Prop by default, with only (ε (fun => True))
       appearing. )

   - N -> recspace A will contain all recursive arguments by emulating lists.
     ( Fnil and FCONS defined below emulate nil and cons. )
     ( Recursive arguments need to be either directly of type B_i for some i or of type T B_i where
       T is an already defined inductive type. In this case, HOL_Light adds another type
       to the mutual definition, TB_i (isomorphic to T B_i), maps T B_i to TB_i and then uses this mapping
       to define the actual constructors with arguments in T B_i. )

   - The first integer argument of CONSTR is used to index constructors.
     ( The first one defined will be assigned 0, the second 1, etc. )
 *)

(* Example of the definition of list A :
  - Defined with recspace A (for the one external argument in cons).
  - nil is the first constructor, so nil = CONSTR 0 (ε (fun _ => True)) Fnil.
  - cons is the second one, so cons a l = CONSTR 1 a (FCONS l Fnil). *)


Definition NFnil {A : Type} : N -> Nrecspace A := fun _ => NBOTTOM.

Definition NFCONS {A : Type} (a : A) (f: N -> A) (n : N) : A :=
  N.recursion a (fun n _ => f n) n.

Notation "[ ]_rec" := NFnil (format "[ ]_rec").
Notation "[ x ]_rec" := (NFCONS x NFnil).
Notation "[ x ; y ; .. ; z ]_rec" := (NFCONS x (NFCONS y .. (NFCONS z NFnil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]_rec").

Instance N_FCONS : FCONS_Class.
Proof.
  exists @NFCONS=>A.
  by N_rec_align => * ; rewrite/NFCONS N.recursion_succ.
Defined.

Canonical N_FCONS.

Fixpoint N_dest_rec {A : Type'} (r : Nrecspace A) : N -> A -> Prop :=
  match r with
  | NBOTTOM => ZBOT A
  | NCONSTR n a f => ZCONSTR A n a (fun m => N_dest_rec (f m)) end.

Definition N_mk_rec {A : Type'} : (N -> A -> Prop) -> Nrecspace A := finv N_dest_rec.

Lemma spec A B (f g : A -> B) x : f = g -> f x = g x.
Proof.
  by move=>->.
Qed.

Ltac spec H x := apply (spec x) in H.

Instance N_recspace : recspace_Class.
Proof.
  exists Nrecspace @N_mk_rec @N_dest_rec.
  - move=>A a ; apply finv_inv_l => {a}.
    induction x0 ; induction x1 => /=.
    + by [].
    + rewrite sym => contra ; destruct (thm_ZCONSTR_ZBOT _ _ _ _ contra).
    + move=> contra ; destruct (thm_ZCONSTR_ZBOT _ _ _ _ contra).
    + rewrite ZCONSTR_def 2!thm_INJP_INJ thm_INJN_INJ thm_INJA_INJ thm_INJF_INJ.
      rewrite thm_SUC_INJ => [[-> [-> Hn0n2]]] ; f_equal.
      by ext => m ; apply H ; spec Hn0n2 m.
  -  intros A P. apply finv_inv_r.
     + induction 1.
       * now exists NBOTTOM.
       * exists (NCONSTR c i (fun n => N_mk_rec (r n))). simpl. f_equal.
         ext 1 =>n. exact (ε_spec (H0 n)).
     + intros (r , <-). induction r ; now constructor.
Defined.

Canonical N_recspace.

Instance N_BOTTOM : BOTTOM_Class.
Proof.
  exists (fun A : Type' => @NBOTTOM A) => A.
  by rewrite-/(N_dest_rec NBOTTOM) axiom_9.
Defined.

Canonical N_BOTTOM.

Instance N_CONSTR : CONSTR_Class.
Proof.
  exists (fun A : Type' => @NCONSTR A) => A /` n a s.
  by rewrite-/(N_dest_rec (NCONSTR n a s)) axiom_9.
Defined.

Canonical N_CONSTR.

Lemma FCONS_inj [A : Type'] (a a' : A) f f' : (NFCONS a f = NFCONS a' f') = (a = a' /\ f = f').
Proof.
  ext => H. split.
  - by spec H 0.
  - ext => n. spec H (N.succ n).
    by rewrite /NFCONS 2!recursion_succ in H.
  - destruct H as (Ha , Hf). apply N.peano_ind.
    + exact Ha.
    + intros n IHn. unfold NFCONS. do 2 rewrite recursion_succ. now rewrite Hf.
Qed.

Ltac _mk_dest_inductive := _mk_dest_inductive0 FCONS_inj.

(****************************************************************************)
(* Alignment of the option type constructor. *)
(****************************************************************************)

(* HOL_Light's option type overwrote Rocq's option type. *)
Notation option := Datatypes.option.

Definition _dest_option : forall {A : Type'}, option A -> recspace A :=
  fun A o =>
    match o with
    | None => NCONSTR 0 (ε (fun _ => True)) []_rec
    | Some a => NCONSTR 1 a []_rec
    end.

Definition _mk_option {A : Type'} := finv (@_dest_option A).

Lemma Naxiom_13 {A : Type'} : forall (a : option A), (@_mk_option A (@_dest_option A a)) = a.
Proof. _mk_dest_inductive. Qed.

Definition option_pred {A : Type'} (r : recspace A) :=
  forall option' : recspace A -> Prop,
      (forall a' : recspace A,
       a' = NCONSTR (NUMERAL N0) (ε (fun _ : A => True)) (fun _ : N => NBOTTOM) \/
       (exists a'' : A, a' = NCONSTR (N.succ (NUMERAL N0)) a'' (fun _ : N => NBOTTOM)) ->
       option' a') -> option' r.

Lemma Naxiom_14 : forall {A : Type'} (r : recspace A), (option_pred r) = ((@_dest_option A (@_mk_option A r)) = r).
Proof.
  intros A r. _dest_mk_inductive. now exists None. now exists (Some x0).
Qed.

Instance N_option : option_Class := {|
  axiom_13 := @Naxiom_13 ;
  axiom_14 := @Naxiom_14 |}.

Canonical N_option.

Lemma NNONE_def (A : Type') :  None = @_mk_option A (CONSTR A (NUMERAL _0) (ε xpredpT) (fun=> BOTTOM A)).
Proof. constr_align (axiom_13 A). Qed.

Instance N_NONE : NONE_Class := {| NONE_def := NNONE_def |}.

Canonical N_NONE.

Lemma NSOME_def (A : Type') : Some = (fun a : A => theory._mk_option A (CONSTR A (SUC (NUMERAL _0)) a (fun=> BOTTOM A))).
Proof. constr_align (axiom_13 A). Qed.

Instance N_SOME : SOME_Class := {| SOME_def := NSOME_def |}.

Canonical N_SOME.

(****************************************************************************)
(* Alignment of the list type constructor. *)
(****************************************************************************)

HB.instance Definition _ A := is_Type' (@nil A).

Require Import Stdlib.Lists.List.

Fixpoint _dest_list {A : Type'} l : recspace A :=
  match l with
  | nil => NCONSTR (NUMERAL N0) (ε (fun _ => True)) []_rec
  | a::l => NCONSTR (N.succ (NUMERAL N0)) a [_dest_list l]_rec
  end.

Definition _mk_list {A : Type'} := finv (@_dest_list A).

Lemma Naxiom_15 {A : Type'} : forall (a : list A), (@_mk_list A (@_dest_list A a)) = a.
Proof. _mk_dest_inductive. Qed.

Definition list_pred {A : Type'} (r : recspace A) :=
  forall list0 : recspace A -> Prop,
  (forall a' : recspace A,
  a' = NCONSTR (NUMERAL N0) (ε (fun _ : A => True)) (fun _ : N => NBOTTOM) \/
  (exists (a0 : A) (a1 : recspace A), a' = NCONSTR (N.succ (NUMERAL N0)) a0 (NFCONS a1 (fun _ : N => NBOTTOM)) /\ list0 a1) -> list0 a')
  -> list0 r.

Lemma Naxiom_16 : forall {A : Type'} (r : recspace A), (list_pred r) = ((@_dest_list A (@_mk_list A r)) = r).
Proof.
  _dest_mk_inductive.
  - now exists nil.
  - exists (cons x0 x2). now rewrite <- H0.
  - right. exists a. exists (_dest_list x0). split.
    reflexivity. now apply IHx0.
Qed.

Instance N_list : list_Class := {|
  axiom_15 := @Naxiom_15 ;
  axiom_16 := @Naxiom_16 |}.

Canonical N_list.

Lemma NNIL_def {A : Type'} : (@nil A) = (@_mk_list A (CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => BOTTOM A))).
Proof. constr_align (axiom_15 A). Qed.

Instance N_NIL : NIL_Class := {| NIL_def := @NNIL_def |}.

Canonical N_NIL.

Lemma NCONS_def {A : Type'} : (@cons A) = (fun a0 : A => fun a1 : list A => @_mk_list A ((fun a0' : A => fun a1' : recspace A => CONSTR A (N.succ (NUMERAL N0)) a0' (FCONS (recspace A) a1' (fun n : N => BOTTOM A))) a0 (@_dest_list A a1))).
Proof. constr_align (axiom_15 A). Qed.

Instance N_CONS : CONS_Class := {| CONS_def := @NCONS_def |}.

Canonical N_CONS.

(****************************************************************************)
(* Tools to align some list functions *)
(****************************************************************************)

Inductive is_nil (A : Type) : list A -> Prop := nil_is_nil : is_nil nil.
Arguments is_nil : clear implicits.

Lemma if_list {A : Type} {B : Type'} {l : list A} {x y : B} : 
  (if l=nil then x else y) = match l with nil => x | _ => y end.
Proof.
  now if_intro ; destruct l.
Qed.

Ltac if_list := rewrite/COND if_list.

(****************************************************************************)
(* Alignment of list functions *)
(****************************************************************************)

Lemma NAPPEND_def {A : Type'} : (@app A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> (list A) -> list A) (fun APPEND' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> (list A) -> list A => forall _17935 : prod N (prod N (prod N (prod N (prod N N)))), (forall l : list A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof.
  total_align.
Qed.

Instance N_APPEND : APPEND_Class := {| APPEND_def := @NAPPEND_def |}.

Canonical N_APPEND.

Lemma NREVERSE_def {A : Type'} : (@rev A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list A) -> list A) (fun REVERSE' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list A) -> list A => forall _17939 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : list A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@app A (REVERSE' _17939 l) (@cons A x (@nil A))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))).
Proof.
  total_align.
Qed.

Instance N_REVERSE : REVERSE_Class := {| REVERSE_def := @NREVERSE_def |}.

Canonical N_REVERSE.

Fixpoint lengthN {A : Type} (l : list A) :=
match l with
|nil => N0
|_::l => N.succ (lengthN l) end.

Lemma length_of_nat_N {A : Type} (l : list A) : N.of_nat (length l) = lengthN l.
Proof.
  induction l ; first by [].
  by rewrite/length Nnat.Nat2N.inj_succ /= -IHl.
Qed.

Lemma NLENGTH_def {A : Type'} : lengthN = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> N) (fun LENGTH' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> N => forall _18106 : prod N (prod N (prod N (prod N (prod N N)))), ((LENGTH' _18106 (@nil A)) = N0) /\ (forall h : A, forall t : list A, (LENGTH' _18106 (@cons A h t)) = (N.succ (LENGTH' _18106 t)))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof.
  total_align.
Qed.

Instance N_LENGTH : LENGTH_Class := {| LENGTH_def := @NLENGTH_def |}.

Canonical N_LENGTH.

Lemma NMAP_def {A B : Type'} : (@map A B) = (@ε ((prod N (prod N N)) -> (A -> B) -> (list A) -> list B) (fun MAP' : (prod N (prod N N)) -> (A -> B) -> (list A) -> list B => forall _17950 : prod N (prod N N), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof.
 total_align2.
Qed.

Instance N_MAP : MAP_Class := {| MAP_def := @NMAP_def |}.

Canonical N_MAP.

Lemma NBUTLAST_def {_25251 : Type'} : (@removelast _25251) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list _25251) -> list _25251) (fun BUTLAST' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list _25251) -> list _25251 => forall _17958 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((BUTLAST' _17958 (@nil _25251)) = (@nil _25251)) /\ (forall h : _25251, forall t : list _25251, (BUTLAST' _17958 (@cons _25251 h t)) = (@COND (list _25251) (t = (@nil _25251)) (@nil _25251) (@cons _25251 h (BUTLAST' _17958 t))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof.
  total_align. by if_list.
Qed.

Instance N_BUTLAST : BUTLAST_Class := {| BUTLAST_def := @NBUTLAST_def |}.

Canonical N_BUTLAST.

Lemma NALL_def {_25307 : Type'} : (@Forall _25307) = (@ε ((prod N (prod N N)) -> (_25307 -> Prop) -> (list _25307) -> Prop) (fun ALL' : (prod N (prod N N)) -> (_25307 -> Prop) -> (list _25307) -> Prop => forall _17973 : prod N (prod N N), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : list _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  total_align=>* ; first by rewrite is_True ; apply Forall_nil.
  by ext=>[H|[]] ; [inversion H | apply Forall_cons].
Qed.

Instance N_ALL : ALL_Class := {| ALL_def := @NALL_def |}.

Canonical N_ALL.

Lemma NPAIRWISE_def {A : Type'} : (@ForallOrdPairs A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> A -> Prop) -> (list A) -> Prop) (fun PAIRWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> A -> Prop) -> (list A) -> Prop => forall _18057 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall r : A -> A -> Prop, (PAIRWISE' _18057 r (@nil A)) = True) /\ (forall h : A, forall r : A -> A -> Prop, forall t : list A, (PAIRWISE' _18057 r (@cons A h t)) = ((@Forall A (r h) t) /\ (PAIRWISE' _18057 r t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  total_align;intros ; first by rewrite is_True ; apply FOP_nil.
  by ext=> [H|[]] ; [inversion H | apply FOP_cons].
Qed.

Instance N_PAIRWISE : PAIRWISE_Class := {| PAIRWISE_def := @NPAIRWISE_def |}.

Canonical N_PAIRWISE.

Lemma NFILTER_def {A : Type'} : (@filter A : (A -> Prop) -> list A -> list A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> Prop) -> (list A) -> list A) (fun FILTER' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> Prop) -> (list A) -> list A => forall _18185 : prod N (prod N (prod N (prod N (prod N N)))), (forall P : A -> Prop, (FILTER' _18185 P (@nil A)) = (@nil A)) /\ (forall h : A, forall P : A -> Prop, forall t : list A, (FILTER' _18185 P (@cons A h t)) = (@COND (list A) (P h) (@cons A h (FILTER' _18185 P t)) (FILTER' _18185 P t)))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).
Proof.
  total_align.
Qed.

Instance N_FILTER : FILTER_Class := {| FILTER_def := @NFILTER_def |}.

Canonical N_FILTER.

Lemma NMEM_def {_25376 : Type'} : (@In _25376) = (@ε ((prod N (prod N N)) -> _25376 -> (list _25376) -> Prop) (fun MEM' : (prod N (prod N N)) -> _25376 -> (list _25376) -> Prop => forall _17995 : prod N (prod N N), (forall x : _25376, (MEM' _17995 x (@nil _25376)) = False) /\ (forall h : _25376, forall x : _25376, forall t : list _25376, (MEM' _17995 x (@cons _25376 h t)) = ((x = h) \/ (MEM' _17995 x t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  total_align ; first by rewrite (sym x).
  by rewrite (sym a).
Qed.

Instance N_MEM : MEM_Class := {| MEM_def := @NMEM_def |}.

Canonical N_MEM.

Fixpoint repeatpos {A : Type} (n : positive) (a : A) : list A :=
match n with
|xH => a::nil
|xO n => let l := repeatpos n a in l++l
|xI n => let l := repeatpos n a in a::l++l end. 

Definition repeatN {A : Type} (n : N) (a : A) : list A :=
match n with
|0 => nil
|Npos n => repeatpos n a end.

Lemma repeatpos_sym {A : Type} (a : A) (p p' : positive) :
  repeatpos p a ++ a :: repeatpos p' a = a :: repeatpos p a ++ repeatpos p' a.
Proof. 
  revert p'. induction p => p' //.
  - by rewrite /= -app_assoc IHp 3!app_comm_cons -IHp ?app_comm_cons app_assoc.
  - rewrite /= -app_assoc IHp 2!app_comm_cons -IHp -app_comm_cons -app_assoc.
    by rewrite app_comm_cons.
Qed.

Lemma repeatN_succ {A : Type} n (a : A) : repeatN (N.succ n) a = a :: repeatN n a.
Proof.
  by case:n => // ; elim => //= p IHp ; rewrite IHp -app_comm_cons repeatpos_sym.
Qed.

(* In case it is needed *)
Lemma repeat_to_nat_N {A : Type} n (a : A) :
  repeat a (N.to_nat n) = repeatN n a.
Proof.
  induction n using N.peano_ind ; first by reflexivity.
  by rewrite repeatN_succ Nnat.N2Nat.inj_succ -IHn.
Qed.

Lemma NREPLICATE_def {A : Type'} : repeatN = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> N -> A -> list A) (fun REPLICATE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> N -> A -> list A => forall _18125 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall x : A, (REPLICATE' _18125 N0 x) = (@nil A)) /\ (forall n : N, forall x : A, (REPLICATE' _18125 (N.succ n) x) = (@cons A x (REPLICATE' _18125 n x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))))))).
Proof.
  N_rec_align. exact repeatN_succ.
Qed.

Instance N_REPLICATE : REPLICATE_Class := {| REPLICATE_def := @NREPLICATE_def |}.

Canonical N_REPLICATE.

Lemma NITLIST_def {A B : Type'} : (fun f l b => fold_right f b l)  = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> (list A) -> B -> B) (fun ITLIST' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> (list A) -> B -> B => forall _18151 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall b : B, (ITLIST' _18151 f (@nil A) b) = b) /\ (forall h : A, forall f : A -> B -> B, forall t : list A, forall b : B, (ITLIST' _18151 f (@cons A h t) b) = (f h (ITLIST' _18151 f t b)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Proof.
  total_align. by rewrite -IHx.
Qed.

Instance N_ITLIST : ITLIST_Class := {| ITLIST_def := @NITLIST_def |}.

Canonical N_ITLIST.

Definition HD {A : Type'} := @ε ((prod N N) -> (list A) -> A) (fun HD' : (prod N N) -> (list A) -> A => forall _17927 : prod N N, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))).

Definition hd {A:Type'} := @hd A (HD nil).

Lemma NHD_def {A : Type'} : @hd A = @HD A.
Proof. unfold HD. partial_align (is_nil A). Qed.

Instance N_HD : HD_Class := {| HD_def := @NHD_def |}.

Canonical N_HD.

Definition TL {A : Type'} := (@ε ((prod N N) -> (list A) -> list A) (fun TL' : (prod N N) -> (list A) -> list A => forall _17931 : prod N N, forall h : A, forall t : list A, (TL' _17931 (@cons A h t)) = t) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).

Definition tl {A : Type'} (l : list A) :=
match l with
| nil => @TL A nil
| cons h t => @tl A (cons h t)
end.

Lemma NTL_def {A : Type'} : @tl A = @TL A.
Proof.
  unfold TL. partial_align (is_nil A).
Qed.

Instance N_TL : TL_Class := {| TL_def := @NTL_def |}.

Canonical N_TL.

Lemma NNULL_def {A : Type'} : is_nil A = (@ε ((prod N (prod N (prod N N))) -> (list A) -> Prop) (fun NULL' : (prod N (prod N (prod N N))) -> (list A) -> Prop => forall _18129 : prod N (prod N (prod N N)), ((NULL' _18129 (@nil A)) = True) /\ (forall h : A, forall t : list A, (NULL' _18129 (@cons A h t)) = False)) (@pair N (prod N (prod N N)) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))).
Proof.
  total_align. rewrite is_True. exists. rewrite is_False. inversion 1.
Qed.

Instance N_NULL : NULL_Class := {| NULL_def := @NNULL_def |}.

Canonical N_NULL.

Lemma NEX_def {A : Type'} : @Exists A = (@ε ((prod N N) -> (A -> Prop) -> (list A) -> Prop) (fun EX' : (prod N N) -> (A -> Prop) -> (list A) -> Prop => forall _18143 : prod N N, (forall P : A -> Prop, (EX' _18143 P (@nil A)) = False) /\ (forall h : A, forall P : A -> Prop, forall t : list A, (EX' _18143 P (@cons A h t)) = ((P h) \/ (EX' _18143 P t)))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))))).
Proof.
  total_align;intros.
  - rewrite is_False. intro H. inversion H.
  - apply prop_ext;intro H. inversion H;auto.
    destruct H. now apply Exists_cons_hd. now apply Exists_cons_tl.
Qed.

Instance N_EX : EX_Class := {| EX_def := @NEX_def |}.

Canonical N_EX.

Lemma NALL2_def {A B : Type'} : @Forall2 A B = (@ε ((prod N (prod N (prod N N))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop) (fun ALL2' : (prod N (prod N (prod N N))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop => forall _18166 : prod N (prod N (prod N N)), (forall P : A -> B -> Prop, forall l2 : list B, (ALL2' _18166 P (@nil A) l2) = (l2 = (@nil B))) /\ (forall h1' : A, forall P : A -> B -> Prop, forall t1 : list A, forall l2 : list B, (ALL2' _18166 P (@cons A h1' t1) l2) = (@COND Prop (l2 = (@nil B)) False ((P h1' (@hd B l2)) /\ (ALL2' _18166 P t1 (@tl B l2)))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))).
Proof.
  total_align.
  - apply prop_ext;intro H. now inversion H. rewrite H. apply Forall2_nil.
  - if_list. apply prop_ext;intro. now inversion H. induction l2.
    destruct H. now apply Forall2_cons.
Qed.

Instance N_ALL2 : ALL2_Class := {| ALL2_def := @NALL2_def |}.

Canonical N_ALL2.

Definition LAST {A : Type'} := (@ε ((prod N (prod N (prod N N))) -> (list A) -> A) (fun LAST' : (prod N (prod N (prod N N))) -> (list A) -> A => forall _18117 : prod N (prod N (prod N N)), forall h : A, forall t : list A, (LAST' _18117 (@cons A h t)) = (@COND A (t = (@nil A)) h (LAST' _18117 t))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).

Definition last {A : Type'} (l : list A) := last l (LAST nil).

Lemma NLAST_def {A : Type'} : last = (@ε ((prod N (prod N (prod N N))) -> (list A) -> A) (fun LAST' : (prod N (prod N (prod N N))) -> (list A) -> A => forall _18117 : prod N (prod N (prod N N)), forall h : A, forall t : list A, (LAST' _18117 (@cons A h t)) = (@COND A (t = (@nil A)) h (LAST' _18117 t))) (@pair N (prod N (prod N N)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).
Proof.
  partial_align (is_nil A). intros. now if_list.
Qed.

Instance N_LAST : LAST_Class := {| LAST_def := @NLAST_def |}.

Canonical N_LAST.

Fixpoint map2 {A B C : Type'} (f : A -> B -> C) (l : list A) (l' : list B) : list C := 
match l with 
|nil => nil 
|a::l => f a (hd l') :: map2 f l (tl l') end.

Lemma NMAP2_def {A B C : Type'} : map2 = (@ε ((prod N (prod N (prod N N))) -> (A -> B -> C) -> (list A) -> (list B) -> list C) (fun MAP2' : (prod N (prod N (prod N N))) -> (A -> B -> C) -> (list A) -> (list B) -> list C => forall _18174 : prod N (prod N (prod N N)), (forall f : A -> B -> C, forall l : list B, (MAP2' _18174 f (@nil A) l) = (@nil C)) /\ (forall h1' : A, forall f : A -> B -> C, forall t1 : list A, forall l : list B, (MAP2' _18174 f (@cons A h1' t1) l) = (@cons C (f h1' (@hd B l)) (MAP2' _18174 f t1 (@tl B l))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))).
Proof.
  total_align.
Qed.

Instance N_MAP2 : MAP2_Class := {| MAP2_def := @NMAP2_def |}.

Canonical N_MAP2.

(* Cannot align with nth : different possible default values *)
Fixpoint nth_partial {A : Type'} n (l : list A) :=
  match n with
  | O => hd l
  | S n => nth_partial n (tl l) end.

Definition Nth {A : Type'} n (l : list A) := nth_partial (N.to_nat n) l.

(* In case it's needed *)
Lemma nth_to_nat_N {A : Type'} :
  forall n (l : list A) default, (length l > n)%coq_nat -> nth_partial n l = nth n l default.
Proof.
  intros n l default H. revert l H. induction n ; intros l H ; destruct l.
  1,3 : destruct (PeanoNat.Nat.nlt_0_r _ H).
  - reflexivity.
  - apply IHn. now apply PeanoNat.lt_S_n.
Qed.

Lemma NEL_def {A : Type'} : Nth = (@ε ((prod N N) -> N -> (list A) -> A) (fun EL' : (prod N N) -> N -> (list A) -> A => forall _18178 : prod N N, (forall l : list A, (EL' _18178 N0 l) = (@hd A l)) /\ (forall n : N, forall l : list A, (EL' _18178 (N.succ n) l) = (EL' _18178 n (@tl A l)))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))).
Proof.
  N_rec_align. intros n l. unfold Nth. now rewrite Nnat.N2Nat.inj_succ.
Qed.

Instance N_EL : EL_Class := {| EL_def := @NEL_def |}.

Canonical N_EL.

Definition ASSOC {A B : Type'} := (@ε ((prod N (prod N (prod N (prod N N)))) -> A -> (list (prod A B)) -> B) (fun ASSOC' : (prod N (prod N (prod N (prod N N)))) -> A -> (list (prod A B)) -> B => forall _18192 : prod N (prod N (prod N (prod N N))), forall h : prod A B, forall a : A, forall t : list (prod A B), (ASSOC' _18192 a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (ASSOC' _18192 a t))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))).

Fixpoint assoc {A B : Type'} (a : A) (l : list (A * B)) := 
match l with
|nil => ASSOC a nil
|c::l => if fst c = a then snd c else assoc a l end.

Lemma NASSOC_def {A B : Type'} : assoc = (@ε ((prod N (prod N (prod N (prod N N)))) -> A -> (list (prod A B)) -> B) (fun ASSOC' : (prod N (prod N (prod N (prod N N)))) -> A -> (list (prod A B)) -> B => forall _18192 : prod N (prod N (prod N (prod N N))), forall h : prod A B, forall a : A, forall t : list (prod A B), (ASSOC' _18192 a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (ASSOC' _18192 a t))) (@pair N (prod N (prod N (prod N N))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))).
Proof. partial_align (is_nil (A*B)). Qed.

Instance N_ASSOC : ASSOC_Class := {| ASSOC_def := @NASSOC_def |}.

Canonical N_ASSOC.

Fixpoint zip {A B : Type'} (l : list A) (l' : list B) := 
match l with
|nil => nil
|a::l => (a,hd l') :: zip l (tl l') end.

(* In case it is needed *)
Lemma zip_combine {A B : Type'} (l : list A) (l' : list B) :
  (length l <= length l')%coq_nat -> zip l l' = combine l l'.
Proof.
  revert l'. induction l ; intros l' H.
  reflexivity. destruct l'.
  - simpl in H. destruct (PeanoNat.Nat.nle_succ_0 _ H).
  - simpl. rewrite IHl. reflexivity. now apply le_S_n.
Qed.

Lemma NZIP_def {A B : Type'} : zip = (@ε ((prod N (prod N N)) -> (list A) -> (list B) -> list (prod A B)) (fun ZIP' : (prod N (prod N N)) -> (list A) -> (list B) -> list (prod A B) => forall _18205 : prod N (prod N N), (forall l2 : list B, (ZIP' _18205 (@nil A) l2) = (@nil (prod A B))) /\ (forall h1' : A, forall t1 : list A, forall l2 : list B, (ZIP' _18205 (@cons A h1' t1) l2) = (@cons (prod A B) (@pair A B h1' (@hd B l2)) (ZIP' _18205 t1 (@tl B l2))))) (@pair N (prod N N) ((BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).
Proof.
  total_align.
Qed.

Instance N_ZIP : ZIP_Class := {| ZIP_def := @NZIP_def |}.

Canonical N_ZIP.

Fixpoint Forallpairs {A B : Type} (f : A -> B -> Prop) (l : list A) (l' : list B) := 
match l with
|nil => True
|a::l => Forall (f a) l' /\ Forallpairs f l l' end.

Lemma NALLPAIRS_def {A B : Type'} : Forallpairs = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop) (fun ALLPAIRS' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop => forall _18213 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : A -> B -> Prop, forall l : list B, (ALLPAIRS' _18213 f (@nil A) l) = True) /\ (forall h : A, forall f : A -> B -> Prop, forall t : list A, forall l : list B, (ALLPAIRS' _18213 f (@cons A h t) l) = ((@List.Forall B (f h) l) /\ (ALLPAIRS' _18213 f t l)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))))).
Proof.
  total_align.
Qed.

Instance N_ALLPAIRS : ALLPAIRS_Class := {| ALLPAIRS_def := @NALLPAIRS_def |}.

Canonical N_ALLPAIRS.

Definition list_of_Nseq {A : Type'} := 
let fix list_of_seq (s : N -> A) (n : nat) :=
match n with
|O => nil
|S n => list_of_seq s n ++ (s (N.of_nat n) :: nil) end in
fun s n => list_of_seq s (N.to_nat n).

Lemma Nlist_of_seq_def {A : Type'} : list_of_Nseq = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> (N -> A) -> N -> list A) (fun list_of_seq' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))))) -> (N -> A) -> N -> list A => forall _18227 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))), (forall s : N -> A, (list_of_seq' _18227 s N0) = (@nil A)) /\ (forall s : N -> A, forall n : N, (list_of_seq' _18227 s (N.succ n)) = (@app A (list_of_seq' _18227 s n) (@cons A (s n) (@nil A))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))))))))))).
Proof.
  N_rec_align. intros s n. unfold list_of_Nseq.
  rewrite Nnat.N2Nat.inj_succ. now rewrite Nnat.N2Nat.id. 
Qed.

Instance N_list_of_seq : list_of_seq_Class := 
  {| list_of_seq_def := @Nlist_of_seq_def |}.

Canonical N_list_of_seq.

Fixpoint fold_right2 {A B C : Type'} (f : A -> B -> C -> C) 
(l : list A) (l' : list B) (c : C) : C := 
match l with 
|nil => c 
|a::l => (f a (hd l') (fold_right2 f l (tl l') c)) end.

Lemma NITLIST2_def {A B C : Type'} : fold_right2 = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C) (fun ITLIST2' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C => forall _18201 : prod N (prod N (prod N (prod N (prod N (prod N N))))), (forall f : A -> B -> C -> C, forall l2 : list B, forall b : C, (ITLIST2' _18201 f (@nil A) l2 b) = b) /\ (forall h1' : A, forall f : A -> B -> C -> C, forall t1 : list A, forall l2 : list B, forall b : C, (ITLIST2' _18201 f (@cons A h1' t1) l2 b) = (f h1' (@hd B l2) (ITLIST2' _18201 f t1 (@tl B l2) b)))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))).
Proof.
  total_align.
Qed.

Instance N_ITLIST2 : ITLIST2_Class := {| ITLIST2_def := @NITLIST2_def |}.

Canonical N_ITLIST2.

(****************************************************************************)
(* Alignment of the type of ASCII characters. *)
(****************************************************************************)

(* Note the mismatch between Rocq's ascii which takes booleans as arguments
and HOL-Light's char which takes propositions as arguments. *)

Require Import Stdlib.Strings.Ascii.

HB.instance Definition _ := is_Type' zero.

Definition _dest_char : ascii -> Nrecspace (Prop*(Prop*(Prop*(Prop*(Prop*(Prop*(Prop*(Prop)))))))) :=
  fun a => match a with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => NCONSTR 0
    ((fun a0 a1 a2 a3 a4 a5 a6 a7 : Prop => (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7)))))))))
    a0 a1 a2 a3 a4 a5 a6 a7) []_rec end.

Definition _mk_char := finv _dest_char.

Lemma Naxiom_17 : forall (a : ascii), (_mk_char (_dest_char a)) = a.
Proof.
  by finv_inv_l ; intros [] [] [=] * ; f_equal ; AllProp.
Qed.

Definition char_pred (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) :=
  forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' =
    ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' r.

Lemma Naxiom_18 : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))),
char_pred r = ((_dest_char (_mk_char r)) = r).
Proof.
  _dest_mk_inductive.
  by exists (Ascii x0 x1 x2 x3 x4 x5 x6 x7)=> /= ; repeat rewrite asboolE.
Qed.

Instance N_char : char_Class := {|
  axiom_17 := Naxiom_17 ;
  axiom_18 := Naxiom_18 |}.

Canonical N_char.

(*****************************************************************************)
(* Alignment of the type nadd of nearly additive sequences of naturals. *)
(*****************************************************************************)

Instance dist_N : dist_Class.
Proof. by eexists. Defined.

Canonical dist_N.

(* Lemma DIST_TRIANGLE x y z : dist (x,z) <= dist (x,y) + dist (y,z).
Proof. unfold dist; simpl. lia. Qed. *)

Instance is_nadd_N : is_nadd_Class.
Proof. by eexists. Defined.

Canonical is_nadd_N.

Search is_nadd.
(*Lemma is_nadd_times n : is_nadd (fun x => n * x).
Proof.
  exists 0. intros x y. simpl. assert (e: x*(n*y)=y*(n*x)). lia.
  rewrite e DIST_REFL. reflexivity.
Qed. *)

Instance nadd_N : nadd_Class := {|
  axiom_19 := mk_dest thm_is_nadd_0 ;
  axiom_20 := dest_mk thm_is_nadd_0 |}.

Canonical nadd_N.

Instance nadd_of_num_N : nadd_of_num_Class.
Proof. by eexists. Defined.

Canonical nadd_of_num_N.

Instance nadd_le_N : nadd_le_Class.
Proof. by eexists. Defined.

Canonical nadd_le_N.

Search nadd_le "thm".

Lemma nadd_le_trans : forall (x y z : nadd),
  nadd_le x y -> nadd_le y z -> nadd_le x z.
Proof. by move=>? y * ; apply thm_NADD_LE_TRANS with (y:=y). Qed.

Add Relation _ nadd_le
    reflexivity proved by thm_NADD_LE_REFL
    transitivity proved by nadd_le_trans
as nadd_le_rel.

Instance nadd_add_N : nadd_add_Class.
Proof. by eexists. Defined.

Canonical nadd_add_N.
(*Lemma is_nadd_add_aux f g : is_nadd f -> is_nadd g -> is_nadd (fun n => f n + g n).
Proof.
  intros [b i] [c j]. exists (b+c). intros x y.
  generalize (i x y); intro ixy. generalize (j x y); intro jxy.
  unfold dist in *; simpl in *. lia.
Qed.

Lemma is_nadd_add f g : is_nadd (fun n => dest_nadd f n + dest_nadd g n).
Proof.
  destruct f as [f hf]. destruct g as [g hg]. simpl.
  apply is_nadd_add_aux. exact hf. exact hg.
Qed.

Lemma nadd_of_num_add p q :
  nadd_of_num (p + q) = nadd_add (nadd_of_num p) (nadd_of_num q).
Proof.
  unfold nadd_add, nadd_of_num. f_equal. ext=> x.
  rewrite axiom_20_aux. 2: apply is_nadd_times.
  rewrite axiom_20_aux. 2: apply is_nadd_times.
  lia.
Qed.

Lemma NADD_ADD_SYM p q : nadd_add p q = nadd_add q p.
Proof. unfold nadd_add. f_equal. ext=>x. lia. Qed.

Lemma NADD_ADD_ASSOC p q r :
  nadd_add (nadd_add p q) r = nadd_add p (nadd_add q r).
Proof.
  unfold nadd_add. f_equal. ext=>x. rewrite !axiom_20_aux. lia.
  apply is_nadd_add. apply is_nadd_add.
Qed. *)

Instance nadd_mul_N : nadd_mul_Class.
Proof. by eexists. Defined.

Canonical nadd_mul_N.

Instance nadd_rinv_N : nadd_rinv_Class.
Proof. by eexists. Defined.

Canonical nadd_rinv_N.

Instance nadd_eq_N : nadd_eq_Class.
Proof. by eexists. Defined.

Canonical nadd_eq_N.

Lemma nadd_eq_sym f g : nadd_eq f g -> nadd_eq g f.
Proof. by move=>* ; rewrite thm_NADD_EQ_SYM. Qed.

Lemma nadd_eq_trans f g h : nadd_eq f g -> nadd_eq g h -> nadd_eq f h.
Proof. by move=>* ; apply thm_NADD_EQ_TRANS with (y := g). Qed.

Add Relation _ nadd_eq
    reflexivity proved by thm_NADD_EQ_REFL
    symmetry proved by nadd_eq_sym
    transitivity proved by nadd_eq_trans
as nadd_eq_rel.

Require Import Stdlib.Setoids.Setoid.

Add Morphism nadd_add
    with signature nadd_eq ==> nadd_eq ==> nadd_eq
      as nadd_add_morph.
Proof. by move=> * ; apply thm_NADD_ADD_WELLDEF. Qed.

Add Morphism nadd_le
    with signature nadd_eq ==> nadd_eq ==> iff
      as nadd_le_morph.
Proof.
  move=> x y eqxy x' y' eqxy' ; split => Hle.
  by apply thm_NADD_LE_WELLDEF_LEMMA with (x:=x) (y:=x').
  by apply thm_NADD_LE_WELLDEF_LEMMA with (x:=y) (y:=y') ; auto using nadd_eq_sym.
Qed.

(*Lemma nadd_add_lcancel x y z : nadd_add x y = nadd_add x z -> y = z.
Proof.
  intro h. destruct x as [x hx]. destruct y as [y hy]. destruct z as [z hz].
  apply subset_eq_compat. unfold nadd_add in h. simpl in h. apply mk_inj in h.
  ext=>a. generalize (ext_fun h a); simpl; intro ha. lia.
  apply is_nadd_add_aux; assumption. apply is_nadd_add_aux; assumption.
Qed.

Lemma NADD_ADD_LCANCEL x y z :
  nadd_eq (nadd_add x y) (nadd_add x z) -> nadd_eq y z.
Proof.
  intro h. destruct x as [x hx]. destruct y as [y hy]. destruct z as [z hz].
  destruct h as [B h]. exists B. intro n. generalize (h n). unfold nadd_add. simpl.
  unfold dest_nadd, mk_nadd. rewrite !dest_mk_aux. unfold dist. simpl. lia.
  apply is_nadd_add_aux; assumption. apply is_nadd_add_aux; assumption.
Qed.
*)

Instance nadd_inv_N : nadd_inv_Class.
Proof. by eexists. Defined.

Canonical nadd_inv_N.

(*****************************************************************************)
(* Alignment of the type hreal of non-negative real numbers. *)
(*****************************************************************************)

Instance hreal_N : hreal_Class := {|
  axiom_21 := mk_dest_quotient nadd_eq ;
  axiom_22 := dest_mk_quotient nadd_eq |}.

Canonical hreal_N.

Instance hreal_of_num_N : hreal_of_num_Class.
Proof. by eexists. Defined.

Canonical hreal_of_num_N.

Instance hreal_add_N : hreal_add_Class.
Proof. by eexists. Defined.

Canonical hreal_add_N.

Search hreal_of_num hreal_add.

(* Lemma succ_eq_add_1 n : N.succ n = n + 1. Proof. lia. Qed.

Lemma hreal_of_num_S n : hreal_of_num (N.succ n) = hreal_add (hreal_of_num n) (hreal_of_num 1).
Proof. rewrite succ_eq_add_1 hreal_add_of_num. reflexivity. Qed.

Lemma hreal_add_sym p q : hreal_add p q = hreal_add q p.
Proof.
  unfold hreal_add. f_equal. ext=>x [y [z [h1 [h2 h3]]]].
  exists z. exists y. split. rewrite NADD_ADD_SYM. exact h1. auto.
  exists z. exists y. split. rewrite NADD_ADD_SYM. exact h1. auto.
Qed. *)

Search hreal_add nadd_add.
(* Lemma hreal_add_of_mk_hreal p q :
  hreal_add (mk_hreal (nadd_eq p)) (mk_hreal (nadd_eq q))
  = mk_hreal (nadd_eq (nadd_add p q)).
Proof.
  unfold hreal_add. apply f_equal. ext=> x h.

  unfold dest_hreal, mk_hreal in h. destruct h as [p' [q' [h1 [h2 h3]]]].
  rewrite dest_mk_aux_quotient in h2. 2: apply is_eq_class_of.
  rewrite dest_mk_aux_quotient in h3. 2: apply is_eq_class_of.
  rewrite h2 h3. exact h1.

  exists p. exists q. split. exact h. unfold dest_hreal, mk_hreal.
  rewrite !dest_mk_aux_quotient. split; reflexivity.
  apply is_eq_class_of. apply is_eq_class_of.
Qed. *)

(* Lemma mk_hreal_nadd_eq p : mk_hreal (nadd_eq (elt_of p)) = p.
Proof.
  unfold mk_hreal. apply mk_quotient_elt_of.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
Qed. *)

(*Lemma hreal_add_is_mk_hreal p q :
  hreal_add p q = mk_hreal (nadd_eq (nadd_add (elt_of p) (elt_of q))).
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q), hreal_add_of_mk_hreal.
  unfold mk_hreal at 3. unfold mk_hreal at 3. rewrite !mk_quotient_elt_of.
  reflexivity.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
Qed.*)

(*Lemma hreal_add_assoc p q r :
  hreal_add (hreal_add p q) r = hreal_add p (hreal_add q r).
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q),
    <- (mk_hreal_nadd_eq r), !hreal_add_of_mk_hreal.
  f_equal. rewrite NADD_ADD_ASSOC. reflexivity.
Qed.

Lemma hreal_add_lcancel p q r : hreal_add p r = hreal_add q r -> p = q.
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q),
    <- (mk_hreal_nadd_eq r), !hreal_add_of_mk_hreal; intro e.
  unfold mk_hreal, mk_quotient in e. apply mk_inj in e.
  2: apply is_eq_class_of. 2: apply is_eq_class_of.
  apply eq_class_elim in e. 2: apply NADD_EQ_REFL.
  rewrite NADD_ADD_SYM (NADD_ADD_SYM (elt_of q)) in e.
  apply NADD_ADD_LCANCEL in e.
  f_equal. apply eq_class_intro. apply nadd_eq_sym. apply nadd_eq_trans.
  exact e.
Qed. *)

Instance hreal_mul_N : hreal_mul_Class.
Proof. by eexists. Defined.

Canonical hreal_mul_N.

Instance hreal_le_N : hreal_le_Class.
Proof. by eexists. Defined.

Canonical hreal_le_N.

(*Lemma hreal_le_refl x : hreal_le x x.
Proof.
  unfold hreal_le.
  match goal with [|- ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i: exists x, Q x). exists True. set (t := elt_of x). exists t. exists t. split.
  rewrite is_True. apply nadd_le_refl.
  assert (h: dest_hreal x t). apply dest_quotient_elt_of. apply NADD_EQ_REFL.
  auto.
  generalize (ε_spec i); intros [x1 [x2 [h1 [h2 h3]]]].
  unfold reverse_coercion. rewrite <- h1.
  apply dest_quotient_elim in h2.
  2: apply NADD_EQ_REFL. 2: apply nadd_eq_sym. 2: apply nadd_eq_trans.
  apply dest_quotient_elim in h3.
  2: apply NADD_EQ_REFL. 2: apply nadd_eq_sym. 2: apply nadd_eq_trans.
  rewrite <- h2, <- h3. reflexivity.
Qed.

Add Relation _ hreal_le
    reflexivity proved by hreal_le_refl
    (*transitivity proved by hreal_le_trans*)
as hreal_le_rel.*)

Instance hreal_inv_N : hreal_inv_Class.
Proof. by eexists. Defined.

Canonical hreal_inv_N.

(*****************************************************************************)
(* Operations on treal (pairs of hreal's). *)
(*****************************************************************************)

Instance treal_of_num_N : treal_of_num_Class.
Proof. by eexists. Defined.

Canonical treal_of_num_N.

Instance treal_neg_N : treal_neg_Class.
Proof. by eexists. Defined.

Canonical treal_neg_N.

Instance treal_add_N : treal_add_Class.
Proof. by eexists. Defined.

Canonical treal_add_N.

Instance treal_mul_N : treal_mul_Class.
Proof. by eexists. Defined.

Canonical treal_mul_N.

Instance treal_le_N : treal_le_Class.
Proof. by eexists. Defined.

Canonical treal_le_N.

Instance treal_inv_N : treal_inv_Class.
Proof. by eexists. Defined.

Canonical treal_inv_N.

Instance treal_eq_N : treal_eq_Class.
Proof. by eexists. Defined.

Canonical treal_eq_N.

(*Lemma treal_le_refl x : treal_le x x.
Proof.
  unfold treal_le. destruct x as [x1 x2]. simpl. apply hreal_le_refl.
Qed.

Add Relation _ treal_le
    reflexivity proved by treal_le_refl
    (*transitivity proved by treal_le_trans*)
as treal_le_rel.*)

Lemma treal_eq_sym x y : treal_eq x y -> treal_eq y x.
Proof. by rewrite thm_TREAL_EQ_SYM. Qed.

Lemma treal_eq_trans x y z : treal_eq x y -> treal_eq y z -> treal_eq x z.
Proof. by move=>* ; apply thm_TREAL_EQ_TRANS with (y:=y). Qed.

Add Relation _ treal_eq
    reflexivity proved by thm_TREAL_EQ_REFL
    symmetry proved by treal_eq_sym
    transitivity proved by treal_eq_trans
as treal_eq_rel.

Add Morphism treal_add
    with signature treal_eq ==> treal_eq ==> treal_eq
      as treal_add_morph.
Proof. by move=> * ; apply thm_TREAL_ADD_WELLDEF. Qed.

Add Morphism treal_le
    with signature treal_eq ==> treal_eq ==> iff
      as treal_le_morph.
Proof.
  by move=>* ; apply ZifyClasses.eq_iff, thm_TREAL_LE_WELLDEF.
Qed.

(*****************************************************************************)
(* HOL-Light definition of real numbers. *)
(*****************************************************************************)

Module HL.
Instance hol_light_reals : Real_Class :=
{| axiom_23 := mk_dest_quotient treal_eq ;
   axiom_24 := dest_mk_quotient treal_eq |}.

Canonical hol_light_reals.

Definition real := quotient treal_eq.

Definition mk_real := mk_quotient treal_eq.
Definition dest_real := dest_quotient treal_eq.

End HL.

(*****************************************************************************)
(* Proof that Rocq's R is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Require Import Stdlib.Reals.Reals.
Open Scope R_scope.

HB.instance Definition _ := is_Type' 0.

Definition Rsup : (R -> Prop) -> R.
Proof.
  intro E. case: (pselect (bound E)); intro h.
  case (pselect (exists x, E x)); intro i.
  destruct (completeness E h i) as [b j]. exact b.
  exact 0. exact 0.
Defined.

Lemma is_lub_Rsup E : bound E -> (exists x, E x) -> is_lub E (Rsup E).
Proof.
  intros h i. unfold Rsup. case (pselect (bound E)); intro h'.
  case (pselect (exists x, E x)); intro i'.
  destruct (completeness E h' i') as [b j]. exact j. contradiction. contradiction.
Qed.

Require Import fourcolor.reals.real.
Import Real.

Definition R_struct : structure := {|
  val := R;
  le := Rle;
  sup := Rsup;
  add := Rplus;
  zero := R0;
  opp := Ropp;
  mul := Rmult;
  one := R1;
  inv := Rinv
|}.

Canonical R_struct.

Lemma Rsup_upper_bound E : has_sup E -> ub E (Rsup E).
Proof.
  intros [i j]. unfold Rsup. case (pselect (bound E)); intro c.
  case (pselect (exists x : R, E x)); intro d.
  destruct (completeness E c d) as [b [k l]]. intros x h. apply k. exact h.
  intros x h. assert (exists x : R, E x). exists x. exact h. contradiction.
  intros x h. assert (exists x : R, E x). exists x. exact h. contradiction.
Qed.

Lemma Rsup_total E x : has_sup E -> down E x \/ Rle (sup E) x.
Proof.
  intros [i [b j]]. case (pselect (down E x)); intro k. auto. right.
  assert (l : bound E). exists b. exact j.
  generalize (is_lub_Rsup l i); intros [m n]. apply n.
  intros y hy.
  unfold down in k. Search (forall P Q, exists2 x, P & Q = _). rewrite exists2E -forallNE in k.
  generalize (k y); intro k'. rewrite not_andE orNp in k'.
  unfold Rle. left. apply Rnot_le_lt. apply k'. exact hy.
Qed.

(* Remark: in fourcolor, le is primitive and eq is defined as the
intersection of le and the inverse of le, but in coq, lt is primitive
and le is defined from lt and Logic.eq. *)

Lemma eq_R_struct : @eq R_struct = @Logic.eq R.
Proof.
  ext=> [x y [h i]| x y h].
  apply Rle_antisym; auto.
  subst y. split; apply Rle_refl.
Qed.

Lemma R_axioms : axioms R_struct.
Proof.
  apply Axioms.
  apply Rle_refl.
  apply Rle_trans.
  apply Rsup_upper_bound.
  apply Rsup_total.
  apply Rplus_le_compat_l.
  intros x y. rewrite eq_R_struct. apply Rplus_comm.
  intros x y z. rewrite eq_R_struct. rewrite -> Rplus_assoc. reflexivity.
  intro x. rewrite eq_R_struct. apply Rplus_0_l.
  intro x. rewrite eq_R_struct. apply Rplus_opp_r.
  apply Rmult_le_compat_l.
  intros x y. rewrite eq_R_struct. apply Rmult_comm.
  intros x y z. rewrite eq_R_struct. rewrite -> Rmult_assoc. reflexivity.
  intros x y z. rewrite eq_R_struct. apply Rmult_plus_distr_l.
  intro x. rewrite eq_R_struct. apply Rmult_1_l.
  intro x. rewrite eq_R_struct. apply Rinv_r.
  rewrite eq_R_struct. apply R1_neq_R0.
Qed.

Definition R_model : model := {|
  model_structure := R_struct;
  model_axioms := R_axioms;
|}.

Lemma eq_R_model :
  @eq (model_structure R_model) = @Logic.eq (val (model_structure R_model)).
Proof. exact eq_R_struct. Qed.

(*****************************************************************************)
(* Proof that real is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Lemma real_add_of_num p q :
  real_of_num (p + q)%N = real_add (real_of_num p) (real_of_num q).
Proof.
  unfold real_of_num, real_add.
  f_equal. rewrite . treal_add_of_num. ext=> [x h | x [p' [q' [h1 [h2 h3]]]]].

  exists (treal_of_num p). exists (treal_of_num q). split. exact h. split.
  rewrite axiom_24_aux. reflexivity. exists (treal_of_num p). reflexivity.
  rewrite axiom_24_aux. reflexivity. exists (treal_of_num q). reflexivity.

  rewrite axiom_24_aux in h2. 2: exists (treal_of_num p); reflexivity.
  rewrite axiom_24_aux in h3. 2: exists (treal_of_num q); reflexivity.
  rewrite h2 h3. exact h1.
Qed.

Definition real_sup : (real -> Prop) -> real.
Proof.
  intro P. case (pselect (exists x, P x)); intro h.
  case (pselect (exists M, forall x, (P x) -> real_le x M)); intro i.
  set (Q := fun M => (forall x : real, P x -> real_le x M) /\
                    (forall M' : real, (forall x : real, P x -> real_le x M')
                                  -> real_le M M')).
  exact (ε Q). exact (real_of_num 0). exact (real_of_num 0).
Defined.

Definition real_struct : structure := {|
  val := real;
  le := real_le;
  sup := real_sup;
  add := real_add;
  zero := real_of_num 0;
  opp := real_neg;
  mul := real_mul;
  one := real_of_num 1;
  inv := real_inv
|}.

Canonical real_struct.

Require Import HOLLight_Real_With_N.theorems.

Lemma real_sup_is_lub E :
  has_sup E -> ub E (real_sup E) /\ (forall b, ub E b -> real_le (real_sup E) b).
Proof.
  intros [i j]. unfold real_sup.
  destruct (pselect (exists x : real, E x)).
  destruct (pselect (exists M : real, forall x : real, E x -> real_le x M)).
  set (Q := fun M : real =>
              (forall x : real, E x -> real_le x M) /\
                (forall M' : real, (forall x : real, E x -> real_le x M') -> real_le M M')).
  assert (k: exists M : real, Q M). apply (thm_REAL_COMPLETE E (conj i j)).
  generalize (ε_spec k); intros [l m]. auto. contradiction. contradiction.
Qed.

Lemma real_sup_upper_bound E : has_sup E -> ub E (real_sup E).
Proof. intro h. apply (proj1 (real_sup_is_lub h)). Qed.

Lemma real_sup_total E x : has_sup E -> down E x \/ real_le (real_sup E) x.
Proof.
  intro h. case (pselect (down E x)); intro k. auto. right.
  generalize (real_sup_is_lub h); intros [i j]. apply j.
  intros y hy.
  unfold down in k. rewrite exists2E -forallNE in k.
  generalize (k y); intro k'. rewrite not_andE orNp in k'.
  apply thm_REAL_LT_IMP_LE. apply k'. apply hy.
Qed.

Lemma eq_real_struct: @eq real_struct = @Logic.eq real.
Proof.
  by ext => x y ; rewrite/eq thm_REAL_LE_ANTISYM.
Qed.

Lemma real_axioms : axioms real_struct.
Proof.
  apply Axioms.
  apply thm_REAL_LE_REFL.
  intros x y z xy yz; apply (thm_REAL_LE_TRANS x y z (conj xy yz)).
  apply real_sup_upper_bound.
  apply real_sup_total.
  intros x y z yz; rewrite -> thm_REAL_LE_LADD; exact yz.
  intros x y. rewrite eq_real_struct. apply thm_REAL_ADD_SYM.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_ADD_ASSOC.
  intro x. rewrite eq_real_struct. apply thm_REAL_ADD_LID.
  intro x. rewrite eq_real_struct. rewrite -> thm_REAL_ADD_SYM. apply thm_REAL_ADD_LINV.
  intros x y z hx yz. apply thm_REAL_LE_LMUL. auto.
  intros x y. rewrite eq_real_struct. apply thm_REAL_MUL_SYM.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_MUL_ASSOC.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_ADD_LDISTRIB.
  intro x. rewrite eq_real_struct. apply thm_REAL_MUL_LID.
  intro x. rewrite eq_real_struct. rewrite -> thm_REAL_MUL_SYM. apply thm_REAL_MUL_LINV.
  unfold one, zero. simpl. rewrite eq_real_struct thm_REAL_OF_NUM_EQ. lia.
Qed.

Definition real_model : model := {|
  model_structure := real_struct;
  model_axioms := real_axioms;
|}.

Lemma eq_real_model:
  @eq (model_structure real_model) = @Logic.eq (val (model_structure real_model)).
Proof. exact eq_real_struct. Qed.

Require Import fourcolor.reals.realcategorical.
Set Bullet Behavior "Strict Subproofs".

Definition R_of_real := @Rmorph_to real_model R_model.
Definition real_of_R := @Rmorph_to R_model real_model.

Lemma R_of_real_of_R r : R_of_real (real_of_R r) = r.
Proof. rewrite <- eq_R_model. apply (@Rmorph_to_inv R_model real_model). Qed.

Lemma real_of_R_of_real r : real_of_R (R_of_real r) = r.
Proof. rewrite <- eq_real_model. apply (@Rmorph_to_inv real_model R_model). Qed.

(*****************************************************************************)
(* Mapping of HOL-Light reals to Rocq reals. *)
(*****************************************************************************)

Definition mk_real : ((prod hreal hreal) -> Prop) -> R := fun x => R_of_real (mk_real x).

Definition dest_real : R -> (prod hreal hreal) -> Prop := fun x => dest_real (real_of_R x).

Lemma axiom_23 : forall (a : R), (mk_real (dest_real a)) = a.
Proof. intro a. unfold mk_real, dest_real. rewrite axiom_23. apply R_of_real_of_R. Qed.

Lemma axiom_24_aux : forall r, (exists x, r = treal_eq x) -> dest_real (mk_real r) = r.
Proof.
  intros c [x h]. unfold dest_real, mk_real.
  rewrite real_of_R_of_real -axiom_24.
  exists x. exact h.
Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof.
  intro c. unfold dest_real, mk_real. rewrite real_of_R_of_real -axiom_24.
  reflexivity.
Qed.

Lemma real_of_R_morph : morphism real_of_R.
Proof. apply Rmorph_toP. Qed.

Lemma R_of_real_morph : morphism R_of_real.
Proof. apply Rmorph_toP. Qed.

Lemma le_morph_R x y : le x y = le (real_of_R x) (real_of_R y).
Proof.
  generalize (morph_le real_of_R_morph x y); intros [h i]. apply prop_ext; auto.
Qed.

Lemma real_le_def : Rle = (fun x1 : R => fun y1 : R => @ε Prop (fun u : Prop => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, ((treal_le x1' y1') = u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  apply funext =>x ; apply funext=>y.
  unfold dest_real. rewrite le_morph_R.
  generalize (real_of_R x); clear x; intro x.
  generalize (real_of_R y); clear y; intro y.
  reflexivity.
Qed.

Lemma add_morph_R x y : real_of_R (add x y) = (add (real_of_R x) (real_of_R y)).
Proof. rewrite <- eq_real_model. apply (morph_add real_of_R_morph). Qed.

Lemma add_eq x y : add x y = R_of_real (add (real_of_R x) (real_of_R y)).
Proof. rewrite <- add_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_add_def : Rplus = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  ext=> x y.
  rewrite add_eq. unfold mk_real. apply f_equal. reflexivity.
Qed.

Lemma mul_morph_R x y : real_of_R (mul x y) = (mul (real_of_R x) (real_of_R y)).
Proof. rewrite <- eq_real_model. apply (morph_mul real_of_R_morph). Qed.

Lemma mul_eq x y : mul x y = R_of_real (mul (real_of_R x) (real_of_R y)).
Proof. rewrite <- mul_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_mul_def : Rmult = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  ext=> x y.
  rewrite mul_eq. unfold mk_real. apply f_equal. reflexivity.
Qed.

Lemma zero_morph_R : real_of_R 0%R = real_of_num 0.
Proof. rewrite <- eq_real_model. apply (morph_zero real_of_R_morph). Qed.

Lemma zero_eq : 0%R = R_of_real (real_of_num 0).
Proof. rewrite <- zero_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma inv_morph_R x : real_of_R (inv x) = inv (real_of_R x).
Proof.
  case (pselect (x = 0%R)); intro h.
  subst x. unfold inv. simpl. rewrite Rinv_0 zero_eq !real_of_R_of_real.
  Set Printing All.
  change (@Logic.eq (real) (real_of_num 0) (real_inv (real_of_num 0))).
  symmetry. apply thm_REAL_INV_0.
  rewrite <- eq_real_model. apply (morph_inv real_of_R_morph).
  rewrite eq_R_model. exact h.
  Unset Printing All.
Qed.

Lemma inv_eq x : inv x = R_of_real (inv (real_of_R x)).
Proof. rewrite <- inv_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_inv_def : Rinv = (fun x : R => mk_real (fun u : prod hreal hreal => exists x' : prod hreal hreal, (treal_eq (treal_inv x') u) /\ (dest_real x x'))).
Proof. ext=>x. rewrite inv_eq. unfold mk_real. reflexivity. Qed.

Lemma neg_morph_R x : real_of_R (opp x) = opp (real_of_R x).
Proof. rewrite <- eq_real_model. apply (morph_opp real_of_R_morph). Qed.

Lemma neg_eq x : opp x = R_of_real (opp (real_of_R x)).
Proof. rewrite <- neg_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_neg_def : Ropp = (fun x1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) /\ (dest_real x1 x1'))).
Proof. ext=>x. rewrite neg_eq. unfold mk_real. reflexivity. Qed.

Lemma one_morph_R : real_of_R 1%R = real_of_num 1.
Proof. rewrite <- eq_real_model. apply (morph_one real_of_R_morph). Qed.

Lemma one_eq : 1%R = R_of_real (real_of_num 1).
Proof. rewrite <- one_morph_R, R_of_real_of_R. reflexivity. Qed.

Definition R_of_N n :=
  match n with
  | N0 => 0
  | N.pos p => IPR p
  end.

Require Import Stdlib.micromega.Lra.

Lemma R_of_N_succ n : R_of_N (N.succ n) = R_of_N n + 1.
Proof.
  destruct n; simpl. unfold IPR. lra. rewrite Rplus_comm. apply succ_IPR.
Qed.

Lemma R_of_N_add p q : R_of_N (p + q)%N = R_of_N p + R_of_N q.
Proof.
  destruct p; destruct q; simpl. lra. unfold IPR. lra. unfold IPR. lra.
  apply plus_IPR.
Qed.

Lemma Npos_succ p : N.pos (Pos.succ p) = (N.pos p + 1)%N.
Proof. lia. Qed.

Lemma treal_eq_of_num_add m n :
  treal_eq (treal_of_num (m + n))
  = treal_eq (treal_add (treal_of_num m) (treal_of_num n)).
Proof.
  apply (@eq_class_intro (prod hreal hreal)). apply treal_eq_sym. apply treal_eq_trans.
  symmetry. apply thm_TREAL_OF_NUM_ADD.
Qed.

Lemma mk_real_treal_eq_add p q :
  mk_real (treal_eq (treal_add (treal_of_num p) (treal_of_num q)))
  = (mk_real (treal_eq (treal_of_num p)) + mk_real (treal_eq (treal_of_num q)))%R.
Proof.
  rewrite add_eq. unfold mk_real. f_equal. rewrite !real_of_R_of_real.
  rewrite <- treal_eq_of_num_add.
  change (real_of_num (p + q) = add (real_of_num p) (real_of_num q)).
  rewrite real_add_of_num. reflexivity.
Qed.

Lemma IPR_eq_mk_real p : IPR p = mk_real (treal_eq (treal_of_num (N.pos p))).
Proof.
  pattern p; revert p; apply Pos.peano_ind.
  apply one_eq.
  intros p hp. rewrite succ_IPR Rplus_comm.
  assert (e: IPR 1 = mk_real (treal_eq (treal_of_num 1))). apply one_eq.
  rewrite hp e Npos_succ -mk_real_treal_eq_add -treal_eq_of_num_add.
  reflexivity.
Qed.

Lemma real_of_num_def : R_of_N = (fun m : N => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)).
Proof.
  ext=>n.
  change (R_of_N n = mk_real (treal_eq (treal_of_num n))).
  destruct n; simpl. apply zero_eq. apply IPR_eq_mk_real.
Qed.

Lemma R_of_N0 : R_of_N 0 = 0%R.
Proof. reflexivity. Qed.

Lemma R_of_N1 : R_of_N 1 = 1%R.
Proof. reflexivity. Qed.

Lemma Rnot_le x y : (~ x <= y) = (x > y).
Proof.
  apply prop_ext; intro h.
  apply Rnot_le_gt. exact h.
  apply Rgt_not_le. exact h.
Qed.

Lemma real_abs_def :
  Rabs = (fun y0 : R => @COND R (Rle (R_of_N (NUMERAL 0)) y0) y0 (Ropp y0)).
Proof.
  ext=>r. rewrite/Rabs/NUMERAL R_of_N0. symmetry. destruct (Rcase_abs r).
  - if_triv using Rgt_not_le.
  - if_triv using Rge_le.
Qed.

Lemma real_div_def : Rdiv = (fun y0 : R => fun y1 : R => Rmult y0 (Rinv y1)).
Proof.
  ext. reflexivity.
Qed.

Lemma real_sub_def : Rminus = (fun y0 : R => fun y1 : R => Rplus y0 (Ropp y1)).
Proof.
  ext. reflexivity.
Qed.

Lemma real_ge_def : Rge = (fun y0 : R => fun y1 : R => Rle y1 y0).
Proof.
  ext=> x y h.
  apply Rge_le. exact h. apply Rle_ge. exact h.
Qed.

Lemma real_gt_def : Rgt = (fun y0 : R => fun y1 : R => Rlt y1 y0).
Proof.
  ext=> x y h.
  apply Rgt_lt. exact h. apply Rlt_gt. exact h.
Qed.

Lemma real_lt_def : Rlt = (fun y0 : R => fun y1 : R => ~ (Rle y1 y0)).
Proof.
  ext=> x y h.
  rewrite Rnot_le. exact h. rewrite Rnot_le in h. exact h.
Qed.

Lemma real_max_def : Rmax = (fun y0 : R => fun y1 : R => @COND R (Rle y0 y1) y1 y0).
Proof.
  ext=> x y. unfold Rmax.
  destruct (Rle_dec x y) ; if_triv.
Qed.

Lemma real_min_def : Rmin = (fun y0 : R => fun y1 : R => @COND R (Rle y0 y1) y0 y1).
Proof.
  ext=> x y. unfold Rmin.
  destruct (Rle_dec x y) ; if_triv.
Qed.

Definition Rpow (r : R) n : R := powerRZ r (Z.of_N n).

(* either leave it like that or adapt the ext n tactic to work within R_scope. *)
Close Scope R_scope.

Lemma real_pow_def : Rpow = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> R -> N -> R) (fun real_pow' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> R -> N -> R => forall _24085 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : R, (real_pow' _24085 x (NUMERAL 0%N)) = (R_of_N (NUMERAL (BIT1 0%N)))) /\ (forall x : R, forall n : N, (real_pow' _24085 x (N.succ n)) = (Rmult x (real_pow' _24085 x n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0%N)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))))))))))).
Proof.
  N_rec_align.
  intros x n. unfold Rpow. rewrite <- !Znat.N_nat_Z.
  rewrite <- !Rfunctions.pow_powerRZ.
  rewrite Nnat.N2Nat.inj_succ. reflexivity.
Qed.

Open Scope R_scope.

Definition Rsgn r := r / Rabs r.

Lemma Rsgn_0 : Rsgn 0 = 0.
Proof. unfold Rsgn. lra. Qed.

Lemma Rsgn_pos r : r > 0 -> Rsgn r = 1.
Proof.
  intro h.
  unfold Rsgn.
  rewrite Rabs_pos_eq. 2: lra.
  rewrite Rdiv_diag. 2: lra.
  reflexivity.
Qed.

Lemma Rsgn_neg r : r < 0 -> Rsgn r = -1.
Proof.
  intro h.
  unfold Rsgn.
  rewrite Rabs_left. 2: assumption.
  rewrite Rdiv_opp_r.
  rewrite Rdiv_diag. 2: lra.
  reflexivity.
Qed.

Lemma real_sgn_def : Rsgn = (fun _26598 : R => @COND R (Rlt (R_of_N (NUMERAL 0%N)) _26598) (R_of_N (NUMERAL (BIT1 0%N))) (@COND R (Rlt _26598 (R_of_N (NUMERAL 0%N))) (Ropp (R_of_N (NUMERAL (BIT1 0%N)))) (R_of_N (NUMERAL 0%N)))).
Proof.
  unfold Rsgn.
  ext=> r. cbn.
  repeat if_intro=>*.
  - now apply Rsgn_pos.
  - now apply Rsgn_neg.
  - replace r with 0 ; lra.
Qed.