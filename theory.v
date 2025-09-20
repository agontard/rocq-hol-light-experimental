Require Import Stdlib.NArith.BinNat mathcomp.classical.classical_sets HOLLight_experimental.HOL_Light.
Section terms.
Class _FALSITY__Class := {
  _FALSITY_ : Prop;
  _FALSITY__def : _FALSITY_ = False }.
Context {_FALSITY__var : _FALSITY__Class}.
Class o_Class := {
  o (A B C : Type') : (B -> C) -> (A -> B) -> A -> C;
  o_def (A B C : Type') : (o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)) }.
Context {o_var : o_Class}.
Class I_Class := {
  I (A : Type') : A -> A;
  I_def (A : Type') : (I A) = (fun x : A => x) }.
Context {I_var : I_Class}.
Class unit_Class := {
  unit : Type';
  one_ABS : Prop -> unit;
  one_REP : unit -> Prop;
  axiom_2 : forall (a : unit), (one_ABS (one_REP a)) = a;
  axiom_3 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r) }.
Context {unit_var : unit_Class}.
Class one_Class := {
  one : unit;
  one_def : one = (@ε unit (fun x : unit => True)) }.
Context {one_var : one_Class}.
Class hashek_Class := {
  hashek : Prop;
  hashek_def : hashek = True }.
Context {hashek_var : hashek_Class}.
Class LET_Class := {
  LET (A B : Type') : (A -> B) -> A -> B;
  LET_def (A B : Type') : (LET A B) = (fun f : A -> B => fun x : A => f x) }.
Context {LET_var : LET_Class}.
Class LET_END_Class := {
  LET_END (A : Type') : A -> A;
  LET_END_def (A : Type') : (LET_END A) = (fun t : A => t) }.
Context {LET_END_var : LET_END_Class}.
Class GABS_Class := {
  GABS (A : Type') : (A -> Prop) -> A;
  GABS_def (A : Type') : (GABS A) = (fun P : A -> Prop => @ε A P) }.
Context {GABS_var : GABS_Class}.
Class GEQ_Class := {
  GEQ (A : Type') : A -> A -> Prop;
  GEQ_def (A : Type') : (GEQ A) = (fun a : A => fun b : A => a = b) }.
Context {GEQ_var : GEQ_Class}.
Class _SEQPATTERN_Class := {
  _SEQPATTERN (A B : Type') : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop;
  _SEQPATTERN_def (A B : Type') : (_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)) }.
Context {_SEQPATTERN_var : _SEQPATTERN_Class}.
Class _UNGUARDED_PATTERN_Class := {
  _UNGUARDED_PATTERN : Prop -> Prop -> Prop;
  _UNGUARDED_PATTERN_def : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p /\ r) }.
Context {_UNGUARDED_PATTERN_var : _UNGUARDED_PATTERN_Class}.
Class _GUARDED_PATTERN_Class := {
  _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop;
  _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)) }.
Context {_GUARDED_PATTERN_var : _GUARDED_PATTERN_Class}.
Class _MATCH_Class := {
  _MATCH (A B : Type') : A -> (A -> B -> Prop) -> B;
  _MATCH_def (A B : Type') : (_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))) }.
Context {_MATCH_var : _MATCH_Class}.
Class _FUNCTION_Class := {
  _FUNCTION (A B : Type') : (A -> B -> Prop) -> A -> B;
  _FUNCTION_def (A B : Type') : (_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))) }.
Context {_FUNCTION_var : _FUNCTION_Class}.
Class CURRY_Class := {
  CURRY (A B C : Type') : ((prod A B) -> C) -> A -> B -> C;
  CURRY_def (A B C : Type') : (CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)) }.
Context {CURRY_var : CURRY_Class}.
Class UNCURRY_Class := {
  UNCURRY (A B C : Type') : (A -> B -> C) -> (prod A B) -> C;
  UNCURRY_def (A B C : Type') : (UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)) }.
Context {UNCURRY_var : UNCURRY_Class}.
Class PASSOC_Class := {
  PASSOC (A B C D : Type') : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D;
  PASSOC_def (A B C D : Type') : (PASSOC A B C D) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322)))) }.
Context {PASSOC_var : PASSOC_Class}.
Class IND_SUC_Class := {
  IND_SUC : ind -> ind;
  IND_SUC_def : IND_SUC = (@ε (ind -> ind) (fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)))) }.
Context {IND_SUC_var : IND_SUC_Class}.
Class IND_0_Class := {
  IND_0 : ind;
  IND_0_def : IND_0 = (@ε ind (fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)))) }.
Context {IND_0_var : IND_0_Class}.
Class NUM_REP_Class := {
  NUM_REP : ind -> Prop;
  NUM_REP_def : NUM_REP = (fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a) }.
Context {NUM_REP_var : NUM_REP_Class}.
Class num_Class := {
  num : Type';
  mk_num : ind -> num;
  dest_num : num -> ind;
  axiom_7 : forall (a : num), (mk_num (dest_num a)) = a;
  axiom_8 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r) }.
Context {num_var : num_Class}.
Class _0_Class := {
  _0 : num;
  _0_def : _0 = (mk_num IND_0) }.
Context {_0_var : _0_Class}.
Class SUC_Class := {
  SUC : num -> num;
  SUC_def : SUC = (fun _2104 : num => mk_num (IND_SUC (dest_num _2104))) }.
Context {SUC_var : SUC_Class}.
Class NUMERAL_Class := {
  NUMERAL : num -> num;
  NUMERAL_def : NUMERAL = (fun _2128 : num => _2128) }.
Context {NUMERAL_var : NUMERAL_Class}.
Class BIT0_Class := {
  BIT0 : num -> num;
  BIT0_def : BIT0 = (@ε (num -> num) (fun fn : num -> num => ((fn (NUMERAL _0)) = (NUMERAL _0)) /\ (forall n : num, (fn (SUC n)) = (SUC (SUC (fn n)))))) }.
Context {BIT0_var : BIT0_Class}.
Class BIT1_Class := {
  BIT1 : num -> num;
  BIT1_def : BIT1 = (fun _2143 : num => SUC (BIT0 _2143)) }.
Context {BIT1_var : BIT1_Class}.
Class PRE_Class := {
  PRE : num -> num;
  PRE_def : PRE = (@ε ((prod num (prod num num)) -> num -> num) (fun PRE' : (prod num (prod num num)) -> num -> num => forall _2151 : prod num (prod num num), ((PRE' _2151 (NUMERAL _0)) = (NUMERAL _0)) /\ (forall n : num, (PRE' _2151 (SUC n)) = n)) (@pair num (prod num num) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))) }.
Context {PRE_var : PRE_Class}.
Class add_Class := {
  add : num -> num -> num;
  add_def : add = (@ε (num -> num -> num -> num) (fun add' : num -> num -> num -> num => forall _2155 : num, (forall n : num, (add' _2155 (NUMERAL _0) n) = n) /\ (forall m : num, forall n : num, (add' _2155 (SUC m) n) = (SUC (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) }.
Context {add_var : add_Class}.
Class mul_Class := {
  mul : num -> num -> num;
  mul_def : mul = (@ε (num -> num -> num -> num) (fun mul' : num -> num -> num -> num => forall _2186 : num, (forall n : num, (mul' _2186 (NUMERAL _0) n) = (NUMERAL _0)) /\ (forall m : num, forall n : num, (mul' _2186 (SUC m) n) = (add (mul' _2186 m n) n))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) }.
Context {mul_var : mul_Class}.
Class EXP_Class := {
  EXP : num -> num -> num;
  EXP_def : EXP = (@ε ((prod num (prod num num)) -> num -> num -> num) (fun EXP' : (prod num (prod num num)) -> num -> num -> num => forall _2224 : prod num (prod num num), (forall m : num, (EXP' _2224 m (NUMERAL _0)) = (NUMERAL (BIT1 _0))) /\ (forall m : num, forall n : num, (EXP' _2224 m (SUC n)) = (mul m (EXP' _2224 m n)))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))) }.
Context {EXP_var : EXP_Class}.
Class le_Class := {
  le : num -> num -> Prop;
  le_def : le = (@ε ((prod num num) -> num -> num -> Prop) (fun le' : (prod num num) -> num -> num -> Prop => forall _2241 : prod num num, (forall m : num, (le' _2241 m (NUMERAL _0)) = (m = (NUMERAL _0))) /\ (forall m : num, forall n : num, (le' _2241 m (SUC n)) = ((m = (SUC n)) \/ (le' _2241 m n)))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))))) }.
Context {le_var : le_Class}.
Class lt_Class := {
  lt : num -> num -> Prop;
  lt_def : lt = (@ε (num -> num -> num -> Prop) (fun lt : num -> num -> num -> Prop => forall _2248 : num, (forall m : num, (lt _2248 m (NUMERAL _0)) = False) /\ (forall m : num, forall n : num, (lt _2248 m (SUC n)) = ((m = n) \/ (lt _2248 m n)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0)))))))) }.
Context {lt_var : lt_Class}.
Class ge_Class := {
  ge : num -> num -> Prop;
  ge_def : ge = (fun _2249 : num => fun _2250 : num => le _2250 _2249) }.
Context {ge_var : ge_Class}.
Class gt_Class := {
  gt : num -> num -> Prop;
  gt_def : gt = (fun _2261 : num => fun _2262 : num => lt _2262 _2261) }.
Context {gt_var : gt_Class}.
Class MAX_Class := {
  MAX : num -> num -> num;
  MAX_def : MAX = (fun _2273 : num => fun _2274 : num => @COND num (le _2273 _2274) _2274 _2273) }.
Context {MAX_var : MAX_Class}.
Class MIN_Class := {
  MIN : num -> num -> num;
  MIN_def : MIN = (fun _2285 : num => fun _2286 : num => @COND num (le _2285 _2286) _2285 _2286) }.
Context {MIN_var : MIN_Class}.
Class EVEN_Class := {
  EVEN : num -> Prop;
  EVEN_def : EVEN = (@ε ((prod num (prod num (prod num num))) -> num -> Prop) (fun EVEN' : (prod num (prod num (prod num num))) -> num -> Prop => forall _2603 : prod num (prod num (prod num num)), ((EVEN' _2603 (NUMERAL _0)) = True) /\ (forall n : num, (EVEN' _2603 (SUC n)) = (~ (EVEN' _2603 n)))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))) }.
Context {EVEN_var : EVEN_Class}.
Class ODD_Class := {
  ODD : num -> Prop;
  ODD_def : ODD = (@ε ((prod num (prod num num)) -> num -> Prop) (fun ODD' : (prod num (prod num num)) -> num -> Prop => forall _2607 : prod num (prod num num), ((ODD' _2607 (NUMERAL _0)) = False) /\ (forall n : num, (ODD' _2607 (SUC n)) = (~ (ODD' _2607 n)))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))) }.
Context {ODD_var : ODD_Class}.
Class minus_Class := {
  minus : num -> num -> num;
  minus_def : minus = (@ε (num -> num -> num -> num) (fun minus' : num -> num -> num -> num => forall _2766 : num, (forall m : num, (minus' _2766 m (NUMERAL _0)) = m) /\ (forall m : num, forall n : num, (minus' _2766 m (SUC n)) = (PRE (minus' _2766 m n)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) }.
Context {minus_var : minus_Class}.
Class FACT_Class := {
  FACT : num -> num;
  FACT_def : FACT = (@ε ((prod num (prod num (prod num num))) -> num -> num) (fun FACT' : (prod num (prod num (prod num num))) -> num -> num => forall _2944 : prod num (prod num (prod num num)), ((FACT' _2944 (NUMERAL _0)) = (NUMERAL (BIT1 _0))) /\ (forall n : num, (FACT' _2944 (SUC n)) = (mul (SUC n) (FACT' _2944 n)))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))) }.
Context {FACT_var : FACT_Class}.
Class DIV_Class := {
  DIV : num -> num -> num;
  DIV_def : DIV = (@ε ((prod num (prod num num)) -> num -> num -> num) (fun q : (prod num (prod num num)) -> num -> num -> num => forall _3086 : prod num (prod num num), exists r : num -> num -> num, forall m : num, forall n : num, @COND Prop (n = (NUMERAL _0)) (((q _3086 m n) = (NUMERAL _0)) /\ ((r m n) = m)) ((m = (add (mul (q _3086 m n) n) (r m n))) /\ (lt (r m n) n))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))) }.
Context {DIV_var : DIV_Class}.
Class MOD_Class := {
  MOD : num -> num -> num;
  MOD_def : MOD = (@ε ((prod num (prod num num)) -> num -> num -> num) (fun r : (prod num (prod num num)) -> num -> num -> num => forall _3087 : prod num (prod num num), forall m : num, forall n : num, @COND Prop (n = (NUMERAL _0)) (((DIV m n) = (NUMERAL _0)) /\ ((r _3087 m n) = m)) ((m = (add (mul (DIV m n) n) (r _3087 m n))) /\ (lt (r _3087 m n) n))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))) }.
Context {MOD_var : MOD_Class}.
Class minimal_Class := {
  minimal : (num -> Prop) -> num;
  minimal_def : minimal = (fun _6536 : num -> Prop => @ε num (fun n : num => (_6536 n) /\ (forall m : num, (lt m n) -> ~ (_6536 m)))) }.
Context {minimal_var : minimal_Class}.
Class WF_Class := {
  WF (A : Type') : (A -> A -> Prop) -> Prop;
  WF_def (A : Type') : (WF A) = (fun _6923 : A -> A -> Prop => forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (_6923 y x) -> ~ (P y))) }.
Context {WF_var : WF_Class}.
Class MEASURE_Class := {
  MEASURE (A : Type') : (A -> num) -> A -> A -> Prop;
  MEASURE_def (A : Type') : (MEASURE A) = (fun _8094 : A -> num => fun x : A => fun y : A => lt (_8094 x) (_8094 y)) }.
Context {MEASURE_var : MEASURE_Class}.
Class NUMPAIR_Class := {
  NUMPAIR : num -> num -> num;
  NUMPAIR_def : NUMPAIR = (fun _17487 : num => fun _17488 : num => mul (EXP (NUMERAL (BIT0 (BIT1 _0))) _17487) (add (mul (NUMERAL (BIT0 (BIT1 _0))) _17488) (NUMERAL (BIT1 _0)))) }.
Context {NUMPAIR_var : NUMPAIR_Class}.
Class NUMFST_Class := {
  NUMFST : num -> num;
  NUMFST_def : NUMFST = (@ε ((prod num (prod num (prod num (prod num (prod num num))))) -> num -> num) (fun X : (prod num (prod num (prod num (prod num (prod num num))))) -> num -> num => forall _17503 : prod num (prod num (prod num (prod num (prod num num)))), exists Y : num -> num, forall x : num, forall y : num, ((X _17503 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))) }.
Context {NUMFST_var : NUMFST_Class}.
Class NUMSND_Class := {
  NUMSND : num -> num;
  NUMSND_def : NUMSND = (@ε ((prod num (prod num (prod num (prod num (prod num num))))) -> num -> num) (fun Y : (prod num (prod num (prod num (prod num (prod num num))))) -> num -> num => forall _17504 : prod num (prod num (prod num (prod num (prod num num)))), forall x : num, forall y : num, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17504 (NUMPAIR x y)) = y)) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))))) }.
Context {NUMSND_var : NUMSND_Class}.
Class NUMSUM_Class := {
  NUMSUM : Prop -> num -> num;
  NUMSUM_def : NUMSUM = (fun _17505 : Prop => fun _17506 : num => @COND num _17505 (SUC (mul (NUMERAL (BIT0 (BIT1 _0))) _17506)) (mul (NUMERAL (BIT0 (BIT1 _0))) _17506)) }.
Context {NUMSUM_var : NUMSUM_Class}.
Class NUMLEFT_Class := {
  NUMLEFT : num -> Prop;
  NUMLEFT_def : NUMLEFT = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> num -> Prop) (fun X : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> num -> Prop => forall _17535 : prod num (prod num (prod num (prod num (prod num (prod num num))))), exists Y : num -> num, forall x : Prop, forall y : num, ((X _17535 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))) }.
Context {NUMLEFT_var : NUMLEFT_Class}.
Class NUMRIGHT_Class := {
  NUMRIGHT : num -> num;
  NUMRIGHT_def : NUMRIGHT = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> num -> num) (fun Y : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> num -> num => forall _17536 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), forall x : Prop, forall y : num, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17536 (NUMSUM x y)) = y)) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))))) }.
Context {NUMRIGHT_var : NUMRIGHT_Class}.
Class INJN_Class := {
  INJN (A : Type') : num -> num -> A -> Prop;
  INJN_def (A : Type') : (INJN A) = (fun _17537 : num => fun n : num => fun a : A => n = _17537) }.
Context {INJN_var : INJN_Class}.
Class INJA_Class := {
  INJA (A : Type') : A -> num -> A -> Prop;
  INJA_def (A : Type') : (INJA A) = (fun _17542 : A => fun n : num => fun b : A => b = _17542) }.
Context {INJA_var : INJA_Class}.
Class INJF_Class := {
  INJF (A : Type') : (num -> num -> A -> Prop) -> num -> A -> Prop;
  INJF_def (A : Type') : (INJF A) = (fun _17549 : num -> num -> A -> Prop => fun n : num => _17549 (NUMFST n) (NUMSND n)) }.
Context {INJF_var : INJF_Class}.
Class INJP_Class := {
  INJP (A : Type') : (num -> A -> Prop) -> (num -> A -> Prop) -> num -> A -> Prop;
  INJP_def (A : Type') : (INJP A) = (fun _17554 : num -> A -> Prop => fun _17555 : num -> A -> Prop => fun n : num => fun a : A => @COND Prop (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)) }.
Context {INJP_var : INJP_Class}.
Class ZCONSTR_Class := {
  ZCONSTR (A : Type') : num -> A -> (num -> num -> A -> Prop) -> num -> A -> Prop;
  ZCONSTR_def (A : Type') : (ZCONSTR A) = (fun _17566 : num => fun _17567 : A => fun _17568 : num -> num -> A -> Prop => INJP A (INJN A (SUC _17566)) (INJP A (INJA A _17567) (INJF A _17568))) }.
Context {ZCONSTR_var : ZCONSTR_Class}.
Class ZBOT_Class := {
  ZBOT (A : Type') : num -> A -> Prop;
  ZBOT_def (A : Type') : (ZBOT A) = (INJP A (INJN A (NUMERAL _0)) (@ε (num -> A -> Prop) (fun z : num -> A -> Prop => True))) }.
Context {ZBOT_var : ZBOT_Class}.
Class ZRECSPACE_Class := {
  ZRECSPACE (A : Type') : (num -> A -> Prop) -> Prop;
  ZRECSPACE_def (A : Type') : (ZRECSPACE A) = (fun a : num -> A -> Prop => forall ZRECSPACE' : (num -> A -> Prop) -> Prop, (forall a' : num -> A -> Prop, ((a' = (ZBOT A)) \/ (exists c : num, exists i : A, exists r : num -> num -> A -> Prop, (a' = (ZCONSTR A c i r)) /\ (forall n : num, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a) }.
Context {ZRECSPACE_var : ZRECSPACE_Class}.
Class recspace_Class := {
  recspace : Type' -> Type';
  _mk_rec : forall (A : Type'), (num -> A -> Prop) -> recspace A;
  _dest_rec : forall (A : Type'), (recspace A) -> num -> A -> Prop;
  axiom_9 : forall (A : Type') (a : recspace A), (_mk_rec A (_dest_rec A a)) = a;
  axiom_10 : forall (A : Type') (r : num -> A -> Prop), (ZRECSPACE A r) = ((_dest_rec A (_mk_rec A r)) = r) }.
Context {recspace_var : recspace_Class}.
Class BOTTOM_Class := {
  BOTTOM (A : Type') : recspace A;
  BOTTOM_def (A : Type') : (BOTTOM A) = (_mk_rec A (ZBOT A)) }.
Context {BOTTOM_var : BOTTOM_Class}.
Class CONSTR_Class := {
  CONSTR (A : Type') : num -> A -> (num -> recspace A) -> recspace A;
  CONSTR_def (A : Type') : (CONSTR A) = (fun _17591 : num => fun _17592 : A => fun _17593 : num -> recspace A => _mk_rec A (ZCONSTR A _17591 _17592 (fun n : num => _dest_rec A (_17593 n)))) }.
Context {CONSTR_var : CONSTR_Class}.
Class FCONS_Class := {
  FCONS (A : Type') : A -> (num -> A) -> num -> A;
  FCONS_def (A : Type') : (FCONS A) = (@ε ((prod num (prod num (prod num (prod num num)))) -> A -> (num -> A) -> num -> A) (fun FCONS' : (prod num (prod num (prod num (prod num num)))) -> A -> (num -> A) -> num -> A => forall _17623 : prod num (prod num (prod num (prod num num))), (forall a : A, forall f : num -> A, (FCONS' _17623 a f (NUMERAL _0)) = a) /\ (forall a : A, forall f : num -> A, forall n : num, (FCONS' _17623 a f (SUC n)) = (f n))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))) }.
Context {FCONS_var : FCONS_Class}.
Class FNIL_Class := {
  FNIL (A : Type') : num -> A;
  FNIL_def (A : Type') : (FNIL A) = (fun _17624 : num => @ε A (fun x : A => True)) }.
Context {FNIL_var : FNIL_Class}.
Class Sum_Class := {
  Sum : Type' -> Type' -> Type';
  _mk_sum : forall (A B : Type'), (recspace (prod A B)) -> Sum A B;
  _dest_sum : forall (A B : Type'), (Sum A B) -> recspace (prod A B);
  axiom_11 : forall (A B : Type') (a : Sum A B), (_mk_sum A B (_dest_sum A B a)) = a;
  axiom_12 : forall (A B : Type') (r : recspace (prod A B)), ((fun a : recspace (prod A B) => forall sum' : (recspace (prod A B)) -> Prop, (forall a' : recspace (prod A B), ((exists a'' : A, a' = ((fun a''' : A => CONSTR (prod A B) (NUMERAL _0) (@pair A B a''' (@ε B (fun v : B => True))) (fun n : num => BOTTOM (prod A B))) a'')) \/ (exists a'' : B, a' = ((fun a''' : B => CONSTR (prod A B) (SUC (NUMERAL _0)) (@pair A B (@ε A (fun v : A => True)) a''') (fun n : num => BOTTOM (prod A B))) a''))) -> sum' a') -> sum' a) r) = ((_dest_sum A B (_mk_sum A B r)) = r) }.
Context {Sum_var : Sum_Class}.
Class INL_Class := {
  INL (A B : Type') : A -> Sum A B;
  INL_def (A B : Type') : (INL A B) = (fun a : A => _mk_sum A B ((fun a' : A => CONSTR (prod A B) (NUMERAL _0) (@pair A B a' (@ε B (fun v : B => True))) (fun n : num => BOTTOM (prod A B))) a)) }.
Context {INL_var : INL_Class}.
Class INR_Class := {
  INR (A B : Type') : B -> Sum A B;
  INR_def (A B : Type') : (INR A B) = (fun a : B => _mk_sum A B ((fun a' : B => CONSTR (prod A B) (SUC (NUMERAL _0)) (@pair A B (@ε A (fun v : A => True)) a') (fun n : num => BOTTOM (prod A B))) a)) }.
Context {INR_var : INR_Class}.
Class OUTL_Class := {
  OUTL (A B : Type') : (Sum A B) -> A;
  OUTL_def (A B : Type') : (OUTL A B) = (@ε ((prod num (prod num (prod num num))) -> (Sum A B) -> A) (fun OUTL' : (prod num (prod num (prod num num))) -> (Sum A B) -> A => forall _17649 : prod num (prod num (prod num num)), forall x : A, (OUTL' _17649 (INL A B x)) = x) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))) }.
Context {OUTL_var : OUTL_Class}.
Class OUTR_Class := {
  OUTR (A B : Type') : (Sum A B) -> B;
  OUTR_def (A B : Type') : (OUTR A B) = (@ε ((prod num (prod num (prod num num))) -> (Sum A B) -> B) (fun OUTR' : (prod num (prod num (prod num num))) -> (Sum A B) -> B => forall _17651 : prod num (prod num (prod num num)), forall y : B, (OUTR' _17651 (INR A B y)) = y) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))) }.
Context {OUTR_var : OUTR_Class}.
Class option_Class := {
  option : Type' -> Type';
  _mk_option : forall (A : Type'), (recspace A) -> option A;
  _dest_option : forall (A : Type'), (option A) -> recspace A;
  axiom_13 : forall (A : Type') (a : option A), (_mk_option A (_dest_option A a)) = a;
  axiom_14 : forall (A : Type') (r : recspace A), ((fun a : recspace A => forall option' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (CONSTR A (NUMERAL _0) (@ε A (fun v : A => True)) (fun n : num => BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => CONSTR A (SUC (NUMERAL _0)) a''' (fun n : num => BOTTOM A)) a''))) -> option' a') -> option' a) r) = ((_dest_option A (_mk_option A r)) = r) }.
Context {option_var : option_Class}.
Class NONE_Class := {
  NONE (A : Type') : option A;
  NONE_def (A : Type') : (NONE A) = (_mk_option A (CONSTR A (NUMERAL _0) (@ε A (fun v : A => True)) (fun n : num => BOTTOM A))) }.
Context {NONE_var : NONE_Class}.
Class SOME_Class := {
  SOME (A : Type') : A -> option A;
  SOME_def (A : Type') : (SOME A) = (fun a : A => _mk_option A ((fun a' : A => CONSTR A (SUC (NUMERAL _0)) a' (fun n : num => BOTTOM A)) a)) }.
Context {SOME_var : SOME_Class}.
Class list_Class := {
  list : Type' -> Type';
  _mk_list : forall (A : Type'), (recspace A) -> list A;
  _dest_list : forall (A : Type'), (list A) -> recspace A;
  axiom_15 : forall (A : Type') (a : list A), (_mk_list A (_dest_list A a)) = a;
  axiom_16 : forall (A : Type') (r : recspace A), ((fun a : recspace A => forall list' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (CONSTR A (NUMERAL _0) (@ε A (fun v : A => True)) (fun n : num => BOTTOM A))) \/ (exists a0 : A, exists a1 : recspace A, (a' = ((fun a0' : A => fun a1' : recspace A => CONSTR A (SUC (NUMERAL _0)) a0' (FCONS (recspace A) a1' (fun n : num => BOTTOM A))) a0 a1)) /\ (list' a1))) -> list' a') -> list' a) r) = ((_dest_list A (_mk_list A r)) = r) }.
Context {list_var : list_Class}.
Class NIL_Class := {
  NIL (A : Type') : list A;
  NIL_def (A : Type') : (NIL A) = (_mk_list A (CONSTR A (NUMERAL _0) (@ε A (fun v : A => True)) (fun n : num => BOTTOM A))) }.
Context {NIL_var : NIL_Class}.
Class CONS_Class := {
  CONS (A : Type') : A -> (list A) -> list A;
  CONS_def (A : Type') : (CONS A) = (fun a0 : A => fun a1 : list A => _mk_list A ((fun a0' : A => fun a1' : recspace A => CONSTR A (SUC (NUMERAL _0)) a0' (FCONS (recspace A) a1' (fun n : num => BOTTOM A))) a0 (_dest_list A a1))) }.
Context {CONS_var : CONS_Class}.
Class ISO_Class := {
  ISO (A B : Type') : (A -> B) -> (B -> A) -> Prop;
  ISO_def (A B : Type') : (ISO A B) = (fun _17732 : A -> B => fun _17733 : B -> A => (forall x : B, (_17732 (_17733 x)) = x) /\ (forall y : A, (_17733 (_17732 y)) = y)) }.
Context {ISO_var : ISO_Class}.
Class HD_Class := {
  HD (A : Type') : (list A) -> A;
  HD_def (A : Type') : (HD A) = (@ε ((prod num num) -> (list A) -> A) (fun HD' : (prod num num) -> (list A) -> A => forall _18090 : prod num num, forall t : list A, forall h : A, (HD' _18090 (CONS A h t)) = h) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))) }.
Context {HD_var : HD_Class}.
Class TL_Class := {
  TL (A : Type') : (list A) -> list A;
  TL_def (A : Type') : (TL A) = (@ε ((prod num num) -> (list A) -> list A) (fun TL' : (prod num num) -> (list A) -> list A => forall _18094 : prod num num, forall h : A, forall t : list A, (TL' _18094 (CONS A h t)) = t) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))) }.
Context {TL_var : TL_Class}.
Class APPEND_Class := {
  APPEND (A : Type') : (list A) -> (list A) -> list A;
  APPEND_def (A : Type') : (APPEND A) = (@ε ((prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> (list A) -> list A) (fun APPEND' : (prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> (list A) -> list A => forall _18098 : prod num (prod num (prod num (prod num (prod num num)))), (forall l : list A, (APPEND' _18098 (NIL A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _18098 (CONS A h t) l) = (CONS A h (APPEND' _18098 t l)))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))))) }.
Context {APPEND_var : APPEND_Class}.
Class REVERSE_Class := {
  REVERSE (A : Type') : (list A) -> list A;
  REVERSE_def (A : Type') : (REVERSE A) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A) (fun REVERSE' : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A => forall _18102 : prod num (prod num (prod num (prod num (prod num (prod num num))))), ((REVERSE' _18102 (NIL A)) = (NIL A)) /\ (forall l : list A, forall x : A, (REVERSE' _18102 (CONS A x l)) = (APPEND A (REVERSE' _18102 l) (CONS A x (NIL A))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))) }.
Context {REVERSE_var : REVERSE_Class}.
Class LENGTH_Class := {
  LENGTH (A : Type') : (list A) -> num;
  LENGTH_def (A : Type') : (LENGTH A) = (@ε ((prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> num) (fun LENGTH' : (prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> num => forall _18106 : prod num (prod num (prod num (prod num (prod num num)))), ((LENGTH' _18106 (NIL A)) = (NUMERAL _0)) /\ (forall h : A, forall t : list A, (LENGTH' _18106 (CONS A h t)) = (SUC (LENGTH' _18106 t)))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))))) }.
Context {LENGTH_var : LENGTH_Class}.
Class MAP_Class := {
  MAP (A B : Type') : (A -> B) -> (list A) -> list B;
  MAP_def (A B : Type') : (MAP A B) = (@ε ((prod num (prod num num)) -> (A -> B) -> (list A) -> list B) (fun MAP' : (prod num (prod num num)) -> (A -> B) -> (list A) -> list B => forall _18113 : prod num (prod num num), (forall f : A -> B, (MAP' _18113 f (NIL A)) = (NIL B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _18113 f (CONS A h t)) = (CONS B (f h) (MAP' _18113 f t)))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))) }.
Context {MAP_var : MAP_Class}.
Class LAST_Class := {
  LAST (A : Type') : (list A) -> A;
  LAST_def (A : Type') : (LAST A) = (@ε ((prod num (prod num (prod num num))) -> (list A) -> A) (fun LAST' : (prod num (prod num (prod num num))) -> (list A) -> A => forall _18117 : prod num (prod num (prod num num)), forall h : A, forall t : list A, (LAST' _18117 (CONS A h t)) = (@COND A (t = (NIL A)) h (LAST' _18117 t))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))) }.
Context {LAST_var : LAST_Class}.
Class BUTLAST_Class := {
  BUTLAST (A : Type') : (list A) -> list A;
  BUTLAST_def (A : Type') : (BUTLAST A) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A) (fun BUTLAST' : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A => forall _18121 : prod num (prod num (prod num (prod num (prod num (prod num num))))), ((BUTLAST' _18121 (NIL A)) = (NIL A)) /\ (forall h : A, forall t : list A, (BUTLAST' _18121 (CONS A h t)) = (@COND (list A) (t = (NIL A)) (NIL A) (CONS A h (BUTLAST' _18121 t))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))) }.
Context {BUTLAST_var : BUTLAST_Class}.
Class REPLICATE_Class := {
  REPLICATE (A : Type') : num -> A -> list A;
  REPLICATE_def (A : Type') : (REPLICATE A) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) -> num -> A -> list A) (fun REPLICATE' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) -> num -> A -> list A => forall _18125 : prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))), (forall x : A, (REPLICATE' _18125 (NUMERAL _0) x) = (NIL A)) /\ (forall n : num, forall x : A, (REPLICATE' _18125 (SUC n) x) = (CONS A x (REPLICATE' _18125 n x)))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))))) }.
Context {REPLICATE_var : REPLICATE_Class}.
Class NULL_Class := {
  NULL (A : Type') : (list A) -> Prop;
  NULL_def (A : Type') : (NULL A) = (@ε ((prod num (prod num (prod num num))) -> (list A) -> Prop) (fun NULL' : (prod num (prod num (prod num num))) -> (list A) -> Prop => forall _18129 : prod num (prod num (prod num num)), ((NULL' _18129 (NIL A)) = True) /\ (forall h : A, forall t : list A, (NULL' _18129 (CONS A h t)) = False)) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))) }.
Context {NULL_var : NULL_Class}.
Class ALL_Class := {
  ALL (A : Type') : (A -> Prop) -> (list A) -> Prop;
  ALL_def (A : Type') : (ALL A) = (@ε ((prod num (prod num num)) -> (A -> Prop) -> (list A) -> Prop) (fun ALL' : (prod num (prod num num)) -> (A -> Prop) -> (list A) -> Prop => forall _18136 : prod num (prod num num), (forall P : A -> Prop, (ALL' _18136 P (NIL A)) = True) /\ (forall h : A, forall P : A -> Prop, forall t : list A, (ALL' _18136 P (CONS A h t)) = ((P h) /\ (ALL' _18136 P t)))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))) }.
Context {ALL_var : ALL_Class}.
Class EX_Class := {
  EX (A : Type') : (A -> Prop) -> (list A) -> Prop;
  EX_def (A : Type') : (EX A) = (@ε ((prod num num) -> (A -> Prop) -> (list A) -> Prop) (fun EX' : (prod num num) -> (A -> Prop) -> (list A) -> Prop => forall _18143 : prod num num, (forall P : A -> Prop, (EX' _18143 P (NIL A)) = False) /\ (forall h : A, forall P : A -> Prop, forall t : list A, (EX' _18143 P (CONS A h t)) = ((P h) \/ (EX' _18143 P t)))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))))) }.
Context {EX_var : EX_Class}.
Class ITLIST_Class := {
  ITLIST (A B : Type') : (A -> B -> B) -> (list A) -> B -> B;
  ITLIST_def (A B : Type') : (ITLIST A B) = (@ε ((prod num (prod num (prod num (prod num (prod num num))))) -> (A -> B -> B) -> (list A) -> B -> B) (fun ITLIST' : (prod num (prod num (prod num (prod num (prod num num))))) -> (A -> B -> B) -> (list A) -> B -> B => forall _18151 : prod num (prod num (prod num (prod num (prod num num)))), (forall f : A -> B -> B, forall b : B, (ITLIST' _18151 f (NIL A) b) = b) /\ (forall h : A, forall f : A -> B -> B, forall t : list A, forall b : B, (ITLIST' _18151 f (CONS A h t) b) = (f h (ITLIST' _18151 f t b)))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))) }.
Context {ITLIST_var : ITLIST_Class}.
Class MEM_Class := {
  MEM (A : Type') : A -> (list A) -> Prop;
  MEM_def (A : Type') : (MEM A) = (@ε ((prod num (prod num num)) -> A -> (list A) -> Prop) (fun MEM' : (prod num (prod num num)) -> A -> (list A) -> Prop => forall _18158 : prod num (prod num num), (forall x : A, (MEM' _18158 x (NIL A)) = False) /\ (forall h : A, forall x : A, forall t : list A, (MEM' _18158 x (CONS A h t)) = ((x = h) \/ (MEM' _18158 x t)))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))) }.
Context {MEM_var : MEM_Class}.
Class ALL2_Class := {
  ALL2 (A B : Type') : (A -> B -> Prop) -> (list A) -> (list B) -> Prop;
  ALL2_def (A B : Type') : (ALL2 A B) = (@ε ((prod num (prod num (prod num num))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop) (fun ALL2' : (prod num (prod num (prod num num))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop => forall _18166 : prod num (prod num (prod num num)), (forall P : A -> B -> Prop, forall l2 : list B, (ALL2' _18166 P (NIL A) l2) = (l2 = (NIL B))) /\ (forall h1' : A, forall P : A -> B -> Prop, forall t1 : list A, forall l2 : list B, (ALL2' _18166 P (CONS A h1' t1) l2) = (@COND Prop (l2 = (NIL B)) False ((P h1' (HD B l2)) /\ (ALL2' _18166 P t1 (TL B l2)))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0))))))))))) }.
Context {ALL2_var : ALL2_Class}.
Class MAP2_Class := {
  MAP2 (A B C : Type') : (A -> B -> C) -> (list A) -> (list B) -> list C;
  MAP2_def (A B C : Type') : (MAP2 A B C) = (@ε ((prod num (prod num (prod num num))) -> (A -> B -> C) -> (list A) -> (list B) -> list C) (fun MAP2' : (prod num (prod num (prod num num))) -> (A -> B -> C) -> (list A) -> (list B) -> list C => forall _18174 : prod num (prod num (prod num num)), (forall f : A -> B -> C, forall l : list B, (MAP2' _18174 f (NIL A) l) = (NIL C)) /\ (forall h1' : A, forall f : A -> B -> C, forall t1 : list A, forall l : list B, (MAP2' _18174 f (CONS A h1' t1) l) = (CONS C (f h1' (HD B l)) (MAP2' _18174 f t1 (TL B l))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0))))))))))) }.
Context {MAP2_var : MAP2_Class}.
Class EL_Class := {
  EL (A : Type') : num -> (list A) -> A;
  EL_def (A : Type') : (EL A) = (@ε ((prod num num) -> num -> (list A) -> A) (fun EL' : (prod num num) -> num -> (list A) -> A => forall _18178 : prod num num, (forall l : list A, (EL' _18178 (NUMERAL _0) l) = (HD A l)) /\ (forall n : num, forall l : list A, (EL' _18178 (SUC n) l) = (EL' _18178 n (TL A l)))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))) }.
Context {EL_var : EL_Class}.
Class FILTER_Class := {
  FILTER (A : Type') : (A -> Prop) -> (list A) -> list A;
  FILTER_def (A : Type') : (FILTER A) = (@ε ((prod num (prod num (prod num (prod num (prod num num))))) -> (A -> Prop) -> (list A) -> list A) (fun FILTER' : (prod num (prod num (prod num (prod num (prod num num))))) -> (A -> Prop) -> (list A) -> list A => forall _18185 : prod num (prod num (prod num (prod num (prod num num)))), (forall P : A -> Prop, (FILTER' _18185 P (NIL A)) = (NIL A)) /\ (forall h : A, forall P : A -> Prop, forall t : list A, (FILTER' _18185 P (CONS A h t)) = (@COND (list A) (P h) (CONS A h (FILTER' _18185 P t)) (FILTER' _18185 P t)))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))) }.
Context {FILTER_var : FILTER_Class}.
Class ASSOC_Class := {
  ASSOC (A B : Type') : A -> (list (prod A B)) -> B;
  ASSOC_def (A B : Type') : (ASSOC A B) = (@ε ((prod num (prod num (prod num (prod num num)))) -> A -> (list (prod A B)) -> B) (fun ASSOC' : (prod num (prod num (prod num (prod num num)))) -> A -> (list (prod A B)) -> B => forall _18192 : prod num (prod num (prod num (prod num num))), forall h : prod A B, forall a : A, forall t : list (prod A B), (ASSOC' _18192 a (CONS (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (ASSOC' _18192 a t))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))) }.
Context {ASSOC_var : ASSOC_Class}.
Class ITLIST2_Class := {
  ITLIST2 (A B C : Type') : (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C;
  ITLIST2_def (A B C : Type') : (ITLIST2 A B C) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C) (fun ITLIST2' : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C => forall _18201 : prod num (prod num (prod num (prod num (prod num (prod num num))))), (forall f : A -> B -> C -> C, forall l2 : list B, forall b : C, (ITLIST2' _18201 f (NIL A) l2 b) = b) /\ (forall h1' : A, forall f : A -> B -> C -> C, forall t1 : list A, forall l2 : list B, forall b : C, (ITLIST2' _18201 f (CONS A h1' t1) l2 b) = (f h1' (HD B l2) (ITLIST2' _18201 f t1 (TL B l2) b)))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))))))))) }.
Context {ITLIST2_var : ITLIST2_Class}.
Class ZIP_Class := {
  ZIP (A B : Type') : (list A) -> (list B) -> list (prod A B);
  ZIP_def (A B : Type') : (ZIP A B) = (@ε ((prod num (prod num num)) -> (list A) -> (list B) -> list (prod A B)) (fun ZIP' : (prod num (prod num num)) -> (list A) -> (list B) -> list (prod A B) => forall _18205 : prod num (prod num num), (forall l2 : list B, (ZIP' _18205 (NIL A) l2) = (NIL (prod A B))) /\ (forall h1' : A, forall t1 : list A, forall l2 : list B, (ZIP' _18205 (CONS A h1' t1) l2) = (CONS (prod A B) (@pair A B h1' (HD B l2)) (ZIP' _18205 t1 (TL B l2))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))) }.
Context {ZIP_var : ZIP_Class}.
Class ALLPAIRS_Class := {
  ALLPAIRS (A B : Type') : (A -> B -> Prop) -> (list A) -> (list B) -> Prop;
  ALLPAIRS_def (A B : Type') : (ALLPAIRS A B) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop) (fun ALLPAIRS' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop => forall _18213 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), (forall f : A -> B -> Prop, forall l : list B, (ALLPAIRS' _18213 f (NIL A) l) = True) /\ (forall h : A, forall f : A -> B -> Prop, forall t : list A, forall l : list B, (ALLPAIRS' _18213 f (CONS A h t) l) = ((ALL B (f h) l) /\ (ALLPAIRS' _18213 f t l)))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))))) }.
Context {ALLPAIRS_var : ALLPAIRS_Class}.
Class PAIRWISE_Class := {
  PAIRWISE (A : Type') : (A -> A -> Prop) -> (list A) -> Prop;
  PAIRWISE_def (A : Type') : (PAIRWISE A) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> A -> Prop) -> (list A) -> Prop) (fun PAIRWISE' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> A -> Prop) -> (list A) -> Prop => forall _18220 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), (forall r : A -> A -> Prop, (PAIRWISE' _18220 r (NIL A)) = True) /\ (forall h : A, forall r : A -> A -> Prop, forall t : list A, (PAIRWISE' _18220 r (CONS A h t)) = ((ALL A (r h) t) /\ (PAIRWISE' _18220 r t)))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))))))) }.
Context {PAIRWISE_var : PAIRWISE_Class}.
Class list_of_seq_Class := {
  list_of_seq (A : Type') : (num -> A) -> num -> list A;
  list_of_seq_def (A : Type') : (list_of_seq A) = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))))) -> (num -> A) -> num -> list A) (fun list_of_seq' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))))) -> (num -> A) -> num -> list A => forall _18227 : prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))))), (forall s : num -> A, (list_of_seq' _18227 s (NUMERAL _0)) = (NIL A)) /\ (forall s : num -> A, forall n : num, (list_of_seq' _18227 s (SUC n)) = (APPEND A (list_of_seq' _18227 s n) (CONS A (s n) (NIL A))))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0))))))))))))))))))) }.
Context {list_of_seq_var : list_of_seq_Class}.
Class char_Class := {
  char : Type';
  _mk_char : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> char;
  _dest_char : char -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))));
  axiom_17 : forall (a : char), (_mk_char (_dest_char a)) = a;
  axiom_18 : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))), ((fun a : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) => forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' = ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL _0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : num => BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' a) r) = ((_dest_char (_mk_char r)) = r) }.
Context {char_var : char_Class}.
Class _22857_Class := {
  _22857 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> char;
  _22857_def : _22857 = (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL _0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : num => BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) }.
Context {_22857_var : _22857_Class}.
Class ASCII_Class := {
  ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> char;
  ASCII_def : ASCII = _22857 }.
Context {ASCII_var : ASCII_Class}.
Class dist_Class := {
  dist : (prod num num) -> num;
  dist_def : dist = (fun _22947 : prod num num => add (minus (@fst num num _22947) (@snd num num _22947)) (minus (@snd num num _22947) (@fst num num _22947))) }.
Context {dist_var : dist_Class}.
Class is_nadd_Class := {
  is_nadd : (num -> num) -> Prop;
  is_nadd_def : is_nadd = (fun _23257 : num -> num => exists B : num, forall m : num, forall n : num, le (dist (@pair num num (mul m (_23257 n)) (mul n (_23257 m)))) (mul B (add m n))) }.
Context {is_nadd_var : is_nadd_Class}.
Class nadd_Class := {
  nadd : Type';
  mk_nadd : (num -> num) -> nadd;
  dest_nadd : nadd -> num -> num;
  axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a;
  axiom_20 : forall (r : num -> num), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r) }.
Context {nadd_var : nadd_Class}.
Class nadd_eq_Class := {
  nadd_eq : nadd -> nadd -> Prop;
  nadd_eq_def : nadd_eq = (fun _23276 : nadd => fun _23277 : nadd => exists B : num, forall n : num, le (dist (@pair num num (dest_nadd _23276 n) (dest_nadd _23277 n))) B) }.
Context {nadd_eq_var : nadd_eq_Class}.
Class nadd_of_num_Class := {
  nadd_of_num : num -> nadd;
  nadd_of_num_def : nadd_of_num = (fun _23288 : num => mk_nadd (fun n : num => mul _23288 n)) }.
Context {nadd_of_num_var : nadd_of_num_Class}.
Class nadd_le_Class := {
  nadd_le : nadd -> nadd -> Prop;
  nadd_le_def : nadd_le = (fun _23295 : nadd => fun _23296 : nadd => exists B : num, forall n : num, le (dest_nadd _23295 n) (add (dest_nadd _23296 n) B)) }.
Context {nadd_le_var : nadd_le_Class}.
Class nadd_add_Class := {
  nadd_add : nadd -> nadd -> nadd;
  nadd_add_def : nadd_add = (fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : num => add (dest_nadd _23311 n) (dest_nadd _23312 n))) }.
Context {nadd_add_var : nadd_add_Class}.
Class nadd_mul_Class := {
  nadd_mul : nadd -> nadd -> nadd;
  nadd_mul_def : nadd_mul = (fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : num => dest_nadd _23325 (dest_nadd _23326 n))) }.
Context {nadd_mul_var : nadd_mul_Class}.
Class nadd_rinv_Class := {
  nadd_rinv : nadd -> num -> num;
  nadd_rinv_def : nadd_rinv = (fun _23462 : nadd => fun n : num => DIV (mul n n) (dest_nadd _23462 n)) }.
Context {nadd_rinv_var : nadd_rinv_Class}.
Class nadd_inv_Class := {
  nadd_inv : nadd -> nadd;
  nadd_inv_def : nadd_inv = (fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv _23476))) }.
Context {nadd_inv_var : nadd_inv_Class}.
Class hreal_Class := {
  hreal : Type';
  mk_hreal : (nadd -> Prop) -> hreal;
  dest_hreal : hreal -> nadd -> Prop;
  axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a;
  axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r) }.
Context {hreal_var : hreal_Class}.
Class hreal_of_num_Class := {
  hreal_of_num : num -> hreal;
  hreal_of_num_def : hreal_of_num = (fun m : num => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u)) }.
Context {hreal_of_num_var : hreal_of_num_Class}.
Class hreal_add_Class := {
  hreal_add : hreal -> hreal -> hreal;
  hreal_add_def : hreal_add = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))) }.
Context {hreal_add_var : hreal_add_Class}.
Class hreal_mul_Class := {
  hreal_mul : hreal -> hreal -> hreal;
  hreal_mul_def : hreal_mul = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))) }.
Context {hreal_mul_var : hreal_mul_Class}.
Class hreal_le_Class := {
  hreal_le : hreal -> hreal -> Prop;
  hreal_le_def : hreal_le = (fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))) }.
Context {hreal_le_var : hreal_le_Class}.
Class hreal_inv_Class := {
  hreal_inv : hreal -> hreal;
  hreal_inv_def : hreal_inv = (fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x'))) }.
Context {hreal_inv_var : hreal_inv_Class}.
Class treal_of_num_Class := {
  treal_of_num : num -> prod hreal hreal;
  treal_of_num_def : treal_of_num = (fun _23721 : num => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL _0))) }.
Context {treal_of_num_var : treal_of_num_Class}.
Class treal_neg_Class := {
  treal_neg : (prod hreal hreal) -> prod hreal hreal;
  treal_neg_def : treal_neg = (fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726)) }.
Context {treal_neg_var : treal_neg_Class}.
Class treal_add_Class := {
  treal_add : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal;
  treal_add_def : treal_add = (fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736))) }.
Context {treal_add_var : treal_add_Class}.
Class treal_mul_Class := {
  treal_mul : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal;
  treal_mul_def : treal_mul = (fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758)))) }.
Context {treal_mul_var : treal_mul_Class}.
Class treal_le_Class := {
  treal_le : (prod hreal hreal) -> (prod hreal hreal) -> Prop;
  treal_le_def : treal_le = (fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779))) }.
Context {treal_le_var : treal_le_Class}.
Class treal_inv_Class := {
  treal_inv : (prod hreal hreal) -> prod hreal hreal;
  treal_inv_def : treal_inv = (fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL _0)) (hreal_of_num (NUMERAL _0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL _0))) (@pair hreal hreal (hreal_of_num (NUMERAL _0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d))))))) }.
Context {treal_inv_var : treal_inv_Class}.
Class treal_eq_Class := {
  treal_eq : (prod hreal hreal) -> (prod hreal hreal) -> Prop;
  treal_eq_def : treal_eq = (fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810))) }.
Context {treal_eq_var : treal_eq_Class}.
Class Real_Class := {
  Real : Type';
  mk_real : ((prod hreal hreal) -> Prop) -> Real;
  dest_real : Real -> (prod hreal hreal) -> Prop;
  axiom_23 : forall (a : Real), (mk_real (dest_real a)) = a;
  axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r) }.
Context {Real_var : Real_Class}.
Class real_of_num_Class := {
  real_of_num : num -> Real;
  real_of_num_def : real_of_num = (fun m : num => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)) }.
Context {real_of_num_var : real_of_num_Class}.
Class real_neg_Class := {
  real_neg : Real -> Real;
  real_neg_def : real_neg = (fun x1 : Real => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) /\ (dest_real x1 x1'))) }.
Context {real_neg_var : real_neg_Class}.
Class real_add_Class := {
  real_add : Real -> Real -> Real;
  real_add_def : real_add = (fun x1 : Real => fun y1 : Real => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))) }.
Context {real_add_var : real_add_Class}.
Class real_mul_Class := {
  real_mul : Real -> Real -> Real;
  real_mul_def : real_mul = (fun x1 : Real => fun y1 : Real => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))) }.
Context {real_mul_var : real_mul_Class}.
Class real_le_Class := {
  real_le : Real -> Real -> Prop;
  real_le_def : real_le = (fun x1 : Real => fun y1 : Real => @ε Prop (fun u : Prop => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, ((treal_le x1' y1') = u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))) }.
Context {real_le_var : real_le_Class}.
Class real_inv_Class := {
  real_inv : Real -> Real;
  real_inv_def : real_inv = (fun x : Real => mk_real (fun u : prod hreal hreal => exists x' : prod hreal hreal, (treal_eq (treal_inv x') u) /\ (dest_real x x'))) }.
Context {real_inv_var : real_inv_Class}.
Class real_sub_Class := {
  real_sub : Real -> Real -> Real;
  real_sub_def : real_sub = (fun _24026 : Real => fun _24027 : Real => real_add _24026 (real_neg _24027)) }.
Context {real_sub_var : real_sub_Class}.
Class real_lt_Class := {
  real_lt : Real -> Real -> Prop;
  real_lt_def : real_lt = (fun _24038 : Real => fun _24039 : Real => ~ (real_le _24039 _24038)) }.
Context {real_lt_var : real_lt_Class}.
Class real_ge_Class := {
  real_ge : Real -> Real -> Prop;
  real_ge_def : real_ge = (fun _24050 : Real => fun _24051 : Real => real_le _24051 _24050) }.
Context {real_ge_var : real_ge_Class}.
Class real_gt_Class := {
  real_gt : Real -> Real -> Prop;
  real_gt_def : real_gt = (fun _24062 : Real => fun _24063 : Real => real_lt _24063 _24062) }.
Context {real_gt_var : real_gt_Class}.
Class real_abs_Class := {
  real_abs : Real -> Real;
  real_abs_def : real_abs = (fun _24074 : Real => @COND Real (real_le (real_of_num (NUMERAL _0)) _24074) _24074 (real_neg _24074)) }.
Context {real_abs_var : real_abs_Class}.
Class real_pow_Class := {
  real_pow : Real -> num -> Real;
  real_pow_def : real_pow = (@ε ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> Real -> num -> Real) (fun real_pow' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> Real -> num -> Real => forall _24085 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), (forall x : Real, (real_pow' _24085 x (NUMERAL _0)) = (real_of_num (NUMERAL (BIT1 _0)))) /\ (forall x : Real, forall n : num, (real_pow' _24085 x (SUC n)) = (real_mul x (real_pow' _24085 x n)))) (@pair num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num (prod num num))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num (prod num num)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@pair num (prod num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@pair num (prod num num) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@pair num num (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))))))))))) }.
Context {real_pow_var : real_pow_Class}.
Class real_div_Class := {
  real_div : Real -> Real -> Real;
  real_div_def : real_div = (fun _24086 : Real => fun _24087 : Real => real_mul _24086 (real_inv _24087)) }.
Context {real_div_var : real_div_Class}.
Class real_max_Class := {
  real_max : Real -> Real -> Real;
  real_max_def : real_max = (fun _24098 : Real => fun _24099 : Real => @COND Real (real_le _24098 _24099) _24099 _24098) }.
Context {real_max_var : real_max_Class}.
Class real_min_Class := {
  real_min : Real -> Real -> Real;
  real_min_def : real_min = (fun _24110 : Real => fun _24111 : Real => @COND Real (real_le _24110 _24111) _24110 _24111) }.
Context {real_min_var : real_min_Class}.
Class real_sgn_Class := {
  real_sgn : Real -> Real;
  real_sgn_def : real_sgn = (fun _26598 : Real => @COND Real (real_lt (real_of_num (NUMERAL _0)) _26598) (real_of_num (NUMERAL (BIT1 _0))) (@COND Real (real_lt _26598 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0)))) }.
Context {real_sgn_var : real_sgn_Class}.
Class sqrt_Class := {
  sqrt : Real -> Real;
  sqrt_def : sqrt = (fun _27149 : Real => @ε Real (fun y : Real => ((real_sgn y) = (real_sgn _27149)) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 _0)))) = (real_abs _27149)))) }.
Context {sqrt_var : sqrt_Class}.
Axiom thm_T_DEF : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Axiom thm_AND_DEF : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Axiom thm_IMP_DEF : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Axiom thm_FORALL_DEF : forall (A : Type'), (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Axiom thm_EXISTS_DEF : forall (A : Type'), (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Axiom thm_OR_DEF : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Axiom thm_F_DEF : False = (forall p : Prop, p).
Axiom thm_NOT_DEF : not = (fun p : Prop => p -> False).
Axiom thm_EXISTS_UNIQUE_DEF : forall (A : Type'), (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Axiom thm__FALSITY_ : _FALSITY_ = False.
Axiom thm_EQ_REFL : forall (A : Type'), forall x : A, x = x.
Axiom thm_REFL_CLAUSE : forall (A : Type'), forall x : A, (x = x) = True.
Axiom thm_EQ_SYM : forall (A : Type'), forall x : A, forall y : A, (x = y) -> y = x.
Axiom thm_EQ_SYM_EQ : forall (A : Type'), forall x : A, forall y : A, (x = y) = (y = x).
Axiom thm_EQ_TRANS : forall (A : Type'), forall x : A, forall y : A, forall z : A, ((x = y) /\ (y = z)) -> x = z.
Axiom thm_BETA_THM : forall (A B : Type'), forall f : A -> B, forall y : A, ((fun x : A => f x) y) = (f y).
Axiom thm_ABS_SIMP : forall (A B : Type'), forall t1 : A, forall t2 : B, ((fun x : B => t1) t2) = t1.
Axiom thm_CONJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3).
Axiom thm_CONJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 /\ t2) = (t2 /\ t1).
Axiom thm_CONJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p /\ q) = (q /\ p)) /\ ((((p /\ q) /\ r) = (p /\ (q /\ r))) /\ (((p /\ (q /\ r)) = (q /\ (p /\ r))) /\ (((p /\ p) = p) /\ ((p /\ (p /\ q)) = (p /\ q))))).
Axiom thm_DISJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 \/ (t2 \/ t3)) = ((t1 \/ t2) \/ t3).
Axiom thm_DISJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 \/ t2) = (t2 \/ t1).
Axiom thm_DISJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p \/ q) = (q \/ p)) /\ ((((p \/ q) \/ r) = (p \/ (q \/ r))) /\ (((p \/ (q \/ r)) = (q \/ (p \/ r))) /\ (((p \/ p) = p) /\ ((p \/ (p \/ q)) = (p \/ q))))).
Axiom thm_IMP_CONJ : forall (p : Prop) (q : Prop) (r : Prop), ((p /\ q) -> r) = (p -> q -> r).
Axiom thm_IMP_CONJ_ALT : forall (q : Prop) (p : Prop) (r : Prop), ((p /\ q) -> r) = (q -> p -> r).
Axiom thm_LEFT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, (p /\ (q \/ r)) = ((p /\ q) \/ (p /\ r)).
Axiom thm_RIGHT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, ((p \/ q) /\ r) = ((p /\ r) \/ (q /\ r)).
Axiom thm_FORALL_SIMP : forall (A : Type'), forall t : Prop, (forall x : A, t) = t.
Axiom thm_EXISTS_SIMP : forall (A : Type'), forall t : Prop, (exists x : A, t) = t.
Axiom thm_EQ_CLAUSES : forall t : Prop, ((True = t) = t) /\ (((t = True) = t) /\ (((False = t) = (~ t)) /\ ((t = False) = (~ t)))).
Axiom thm_NOT_CLAUSES_WEAK : ((~ True) = False) /\ ((~ False) = True).
Axiom thm_AND_CLAUSES : forall t : Prop, ((True /\ t) = t) /\ (((t /\ True) = t) /\ (((False /\ t) = False) /\ (((t /\ False) = False) /\ ((t /\ t) = t)))).
Axiom thm_OR_CLAUSES : forall t : Prop, ((True \/ t) = True) /\ (((t \/ True) = True) /\ (((False \/ t) = t) /\ (((t \/ False) = t) /\ ((t \/ t) = t)))).
Axiom thm_IMP_CLAUSES : forall t : Prop, ((True -> t) = t) /\ (((t -> True) = True) /\ (((False -> t) = True) /\ (((t -> t) = True) /\ ((t -> False) = (~ t))))).
Axiom thm_EXISTS_UNIQUE_THM : forall (A : Type'), forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = ((exists x : A, P x) /\ (forall x : A, forall x' : A, ((P x) /\ (P x')) -> x = x')).
Axiom thm_EXISTS_REFL : forall (A : Type'), forall a : A, exists x : A, x = a.
Axiom thm_EXISTS_UNIQUE_REFL : forall (A : Type'), forall a : A, @ex1 A (fun x : A => x = a).
Axiom thm_UNWIND_THM1 : forall (A : Type'), forall P : A -> Prop, forall a : A, (exists x : A, (a = x) /\ (P x)) = (P a).
Axiom thm_UNWIND_THM2 : forall (A : Type'), forall P : A -> Prop, forall a : A, (exists x : A, (x = a) /\ (P x)) = (P a).
Axiom thm_FORALL_UNWIND_THM2 : forall (A : Type'), forall P : A -> Prop, forall a : A, (forall x : A, (x = a) -> P x) = (P a).
Axiom thm_FORALL_UNWIND_THM1 : forall (A : Type'), forall P : A -> Prop, forall a : A, (forall x : A, (a = x) -> P x) = (P a).
Axiom thm_SWAP_FORALL_THM : forall (A B : Type'), forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall y : B, forall x : A, P x y).
Axiom thm_SWAP_EXISTS_THM : forall (A B : Type'), forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists y : B, exists x : A, P x y).
Axiom thm_FORALL_AND_THM : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, (forall x : A, (P x) /\ (Q x)) = ((forall x : A, P x) /\ (forall x : A, Q x)).
Axiom thm_AND_FORALL_THM : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, ((forall x : A, P x) /\ (forall x : A, Q x)) = (forall x : A, (P x) /\ (Q x)).
Axiom thm_LEFT_AND_FORALL_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) /\ Q) = (forall x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_FORALL_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (P /\ (forall x : A, Q x)) = (forall x : A, P /\ (Q x)).
Axiom thm_EXISTS_OR_THM : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, (exists x : A, (P x) \/ (Q x)) = ((exists x : A, P x) \/ (exists x : A, Q x)).
Axiom thm_OR_EXISTS_THM : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, ((exists x : A, P x) \/ (exists x : A, Q x)) = (exists x : A, (P x) \/ (Q x)).
Axiom thm_LEFT_OR_EXISTS_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) \/ Q) = (exists x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_EXISTS_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (P \/ (exists x : A, Q x)) = (exists x : A, P \/ (Q x)).
Axiom thm_LEFT_EXISTS_AND_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) /\ Q) = ((exists x : A, P x) /\ Q).
Axiom thm_RIGHT_EXISTS_AND_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (exists x : A, P /\ (Q x)) = (P /\ (exists x : A, Q x)).
Axiom thm_TRIV_EXISTS_AND_THM : forall (A : Type'), forall P : Prop, forall Q : Prop, (exists x : A, P /\ Q) = ((exists x : A, P) /\ (exists x : A, Q)).
Axiom thm_LEFT_AND_EXISTS_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) /\ Q) = (exists x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_EXISTS_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (P /\ (exists x : A, Q x)) = (exists x : A, P /\ (Q x)).
Axiom thm_TRIV_AND_EXISTS_THM : forall (A : Type'), forall P : Prop, forall Q : Prop, ((exists x : A, P) /\ (exists x : A, Q)) = (exists x : A, P /\ Q).
Axiom thm_TRIV_FORALL_OR_THM : forall (A : Type'), forall P : Prop, forall Q : Prop, (forall x : A, P \/ Q) = ((forall x : A, P) \/ (forall x : A, Q)).
Axiom thm_TRIV_OR_FORALL_THM : forall (A : Type'), forall P : Prop, forall Q : Prop, ((forall x : A, P) \/ (forall x : A, Q)) = (forall x : A, P \/ Q).
Axiom thm_RIGHT_IMP_FORALL_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (P -> forall x : A, Q x) = (forall x : A, P -> Q x).
Axiom thm_RIGHT_FORALL_IMP_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (forall x : A, P -> Q x) = (P -> forall x : A, Q x).
Axiom thm_LEFT_IMP_EXISTS_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) -> Q) = (forall x : A, (P x) -> Q).
Axiom thm_LEFT_FORALL_IMP_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) -> Q) = ((exists x : A, P x) -> Q).
Axiom thm_TRIV_FORALL_IMP_THM : forall (A : Type'), forall P : Prop, forall Q : Prop, (forall x : A, P -> Q) = ((exists x : A, P) -> forall x : A, Q).
Axiom thm_TRIV_EXISTS_IMP_THM : forall (A : Type'), forall P : Prop, forall Q : Prop, (exists x : A, P -> Q) = ((forall x : A, P) -> exists x : A, Q).
Axiom thm_MONO_FORALL : forall (A : Type') (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (forall x : A, P x) -> forall x : A, Q x.
Axiom thm_MONO_EXISTS : forall (A : Type') (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (exists x : A, P x) -> exists x : A, Q x.
Axiom thm_WLOG_RELATION : forall (A : Type'), forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (P x y) -> P y x) /\ ((forall x : A, forall y : A, (R' x y) \/ (R' y x)) /\ (forall x : A, forall y : A, (R' x y) -> P x y))) -> forall x : A, forall y : A, P x y.
Axiom thm_EXISTS_UNIQUE_ALT : forall (A : Type'), forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, forall y : A, (P y) = (x = y)).
Axiom thm_EXISTS_UNIQUE : forall (A : Type'), forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, (P x) /\ (forall y : A, (P y) -> y = x)).
Axiom thm_ETA_AX : forall (A B : Type'), forall t : A -> B, (fun x : A => t x) = t.
Axiom thm_EQ_EXT : forall (A B : Type'), forall f : A -> B, forall g : A -> B, (forall x : A, (f x) = (g x)) -> f = g.
Axiom thm_FUN_EQ_THM : forall (A B : Type'), forall f : A -> B, forall g : A -> B, (f = g) = (forall x : A, (f x) = (g x)).
Axiom thm_SELECT_AX : forall (A : Type'), forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Axiom thm_EXISTS_THM : forall (A : Type'), (@ex A) = (fun P : A -> Prop => P (@ε A P)).
Axiom thm_SELECT_REFL : forall (A : Type'), forall x : A, (@ε A (fun y : A => y = x)) = x.
Axiom thm_SELECT_UNIQUE : forall (A : Type'), forall P : A -> Prop, forall x : A, (forall y : A, (P y) = (y = x)) -> (@ε A P) = x.
Axiom thm_EXCLUDED_MIDDLE : forall t : Prop, t \/ (~ t).
Axiom thm_BOOL_CASES_AX : forall t : Prop, (t = True) \/ (t = False).
Axiom thm_DE_MORGAN_THM : forall t1 : Prop, forall t2 : Prop, ((~ (t1 /\ t2)) = ((~ t1) \/ (~ t2))) /\ ((~ (t1 \/ t2)) = ((~ t1) /\ (~ t2))).
Axiom thm_NOT_CLAUSES : (forall t : Prop, (~ (~ t)) = t) /\ (((~ True) = False) /\ ((~ False) = True)).
Axiom thm_NOT_IMP : forall t1 : Prop, forall t2 : Prop, (~ (t1 -> t2)) = (t1 /\ (~ t2)).
Axiom thm_CONTRAPOS_THM : forall t1 : Prop, forall t2 : Prop, ((~ t1) -> ~ t2) = (t2 -> t1).
Axiom thm_NOT_EXISTS_THM : forall (A : Type'), forall P : A -> Prop, (~ (exists x : A, P x)) = (forall x : A, ~ (P x)).
Axiom thm_EXISTS_NOT_THM : forall (A : Type'), forall P : A -> Prop, (exists x : A, ~ (P x)) = (~ (forall x : A, P x)).
Axiom thm_NOT_FORALL_THM : forall (A : Type'), forall P : A -> Prop, (~ (forall x : A, P x)) = (exists x : A, ~ (P x)).
Axiom thm_FORALL_NOT_THM : forall (A : Type'), forall P : A -> Prop, (forall x : A, ~ (P x)) = (~ (exists x : A, P x)).
Axiom thm_FORALL_BOOL_THM : forall (P : Prop -> Prop), (forall b : Prop, P b) = ((P True) /\ (P False)).
Axiom thm_EXISTS_BOOL_THM : forall (P : Prop -> Prop), (exists b : Prop, P b) = ((P True) \/ (P False)).
Axiom thm_LEFT_FORALL_OR_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) \/ Q) = ((forall x : A, P x) \/ Q).
Axiom thm_RIGHT_FORALL_OR_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (forall x : A, P \/ (Q x)) = (P \/ (forall x : A, Q x)).
Axiom thm_LEFT_OR_FORALL_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) \/ Q) = (forall x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_FORALL_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (P \/ (forall x : A, Q x)) = (forall x : A, P \/ (Q x)).
Axiom thm_LEFT_IMP_FORALL_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) -> Q) = (exists x : A, (P x) -> Q).
Axiom thm_LEFT_EXISTS_IMP_THM : forall (A : Type'), forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) -> Q) = ((forall x : A, P x) -> Q).
Axiom thm_RIGHT_IMP_EXISTS_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (P -> exists x : A, Q x) = (exists x : A, P -> Q x).
Axiom thm_RIGHT_EXISTS_IMP_THM : forall (A : Type'), forall P : Prop, forall Q : A -> Prop, (exists x : A, P -> Q x) = (P -> exists x : A, Q x).
Axiom thm_COND_DEF : forall (A : Type'), (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Axiom thm_COND_CLAUSES : forall (A : Type'), forall t1 : A, forall t2 : A, ((@COND A True t1 t2) = t1) /\ ((@COND A False t1 t2) = t2).
Axiom thm_COND_EXPAND : forall b : Prop, forall t1 : Prop, forall t2 : Prop, (@COND Prop b t1 t2) = (((~ b) \/ t1) /\ (b \/ t2)).
Axiom thm_COND_ID : forall (A : Type'), forall b : Prop, forall t : A, (@COND A b t t) = t.
Axiom thm_COND_RAND : forall (A B : Type'), forall b : Prop, forall f : A -> B, forall x : A, forall y : A, (f (@COND A b x y)) = (@COND B b (f x) (f y)).
Axiom thm_COND_RATOR : forall (A B : Type'), forall b : Prop, forall f : A -> B, forall g : A -> B, forall x : A, (@COND (A -> B) b f g x) = (@COND B b (f x) (g x)).
Axiom thm_COND_ABS : forall (A B : Type'), forall b : Prop, forall f : A -> B, forall g : A -> B, (fun x : A => @COND B b (f x) (g x)) = (@COND (A -> B) b f g).
Axiom thm_COND_SWAP : forall (A : Type'), forall p : Prop, forall x : A, forall y : A, (@COND A (~ p) x y) = (@COND A p y x).
Axiom thm_MONO_COND : forall (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop), ((A -> B) /\ (C -> D)) -> (@COND Prop b A C) -> @COND Prop b B D.
Axiom thm_COND_ELIM_THM : forall (A : Type') (x : A) (c : Prop) (P : A -> Prop) (y : A), (P (@COND A c x y)) = ((c -> P x) /\ ((~ c) -> P y)).
Axiom thm_SKOLEM_THM : forall (A B : Type'), forall P : A -> B -> Prop, (forall x : A, exists y : B, P x y) = (exists y : A -> B, forall x : A, P x (y x)).
Axiom thm_SKOLEM_THM_GEN : forall (A B : Type'), forall P : A -> Prop, forall R' : A -> B -> Prop, (forall x : A, (P x) -> exists y : B, R' x y) = (exists f : A -> B, forall x : A, (P x) -> R' x (f x)).
Axiom thm_UNIQUE_SKOLEM_ALT : forall (A B : Type'), forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (exists f : A -> B, forall x : A, forall y : B, (P x y) = ((f x) = y)).
Axiom thm_UNIQUE_SKOLEM_THM : forall (A B : Type'), forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (@ex1 (A -> B) (fun f : A -> B => forall x : A, P x (f x))).
Axiom thm_bool_INDUCT : forall P : Prop -> Prop, ((P False) /\ (P True)) -> forall x : Prop, P x.
Axiom thm_bool_RECURSION : forall (A : Type'), forall a : A, forall b : A, exists f : Prop -> A, ((f False) = a) /\ ((f True) = b).
Axiom thm_o_DEF : forall (A B C : Type'), forall f : B -> C, forall g : A -> B, (o A B C f g) = (fun x : A => f (g x)).
Axiom thm_I_DEF : forall (A : Type'), (I A) = (fun x : A => x).
Axiom thm_o_THM : forall (A B C : Type'), forall f : B -> C, forall g : A -> B, forall x : A, (o A B C f g x) = (f (g x)).
Axiom thm_o_ASSOC : forall (A B C D : Type'), forall f : C -> D, forall g : B -> C, forall h : A -> B, (o A C D f (o A B C g h)) = (o A B D (o B C D f g) h).
Axiom thm_I_THM : forall (A : Type'), forall x : A, (I A x) = x.
Axiom thm_I_O_ID : forall (A B : Type'), forall f : A -> B, ((o A B B (I B) f) = f) /\ ((o A A B f (I A)) = f).
Axiom thm_EXISTS_ONE_REP : exists b : Prop, b.
Axiom thm_one_DEF : one = (@ε unit (fun x : unit => True)).
Axiom thm_one : forall v : unit, v = one.
Axiom thm_one_axiom : forall (A : Type'), forall f : A -> unit, forall g : A -> unit, f = g.
Axiom thm_one_INDUCT : forall P : unit -> Prop, (P one) -> forall x : unit, P x.
Axiom thm_one_RECURSION : forall (A : Type'), forall e : A, exists fn : unit -> A, (fn one) = e.
Axiom thm_one_Axiom : forall (A : Type'), forall e : A, @ex1 (unit -> A) (fun fn : unit -> A => (fn one) = e).
Axiom thm_FORALL_ONE_THM : forall (P : unit -> Prop), (forall x : unit, P x) = (P one).
Axiom thm_EXISTS_ONE_THM : forall (P : unit -> Prop), (exists x : unit, P x) = (P one).
Axiom thm_ETA_ONE : forall (A : Type'), forall f : unit -> A, (fun x : unit => f one) = f.
Axiom thm_LET_DEF : forall (A B : Type'), forall f : A -> B, forall x : A, (LET A B f x) = (f x).
Axiom thm_LET_END_DEF : forall (A : Type'), forall t : A, (LET_END A t) = t.
Axiom thm_GABS_DEF : forall (A : Type'), forall P : A -> Prop, (GABS A P) = (@ε A P).
Axiom thm_GEQ_DEF : forall (A : Type'), forall a : A, forall b : A, (GEQ A a b) = (a = b).
Axiom thm__SEQPATTERN : forall (A B : Type'), (_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Axiom thm__UNGUARDED_PATTERN : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p /\ r).
Axiom thm__GUARDED_PATTERN : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Axiom thm__MATCH : forall (A B : Type'), (_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Axiom thm__FUNCTION : forall (A B : Type'), (_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Axiom thm_mk_pair_def : forall (A B : Type'), forall x : A, forall y : B, (@mk_pair A B x y) = (fun a : A => fun b : B => (a = x) /\ (b = y)).
Axiom thm_PAIR_EXISTS_THM : forall (A B : Type'), exists x : A -> B -> Prop, exists a : A, exists b : B, x = (@mk_pair A B a b).
Axiom thm_REP_ABS_PAIR : forall (A B : Type'), forall x : A, forall y : B, (@REP_prod A B (@ABS_prod A B (@mk_pair A B x y))) = (@mk_pair A B x y).
Axiom thm_COMMA_DEF : forall (A B : Type'), forall x : A, forall y : B, (@pair A B x y) = (@ABS_prod A B (@mk_pair A B x y)).
Axiom thm_FST_DEF : forall (A B : Type'), forall p : prod A B, (@fst A B p) = (@ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Axiom thm_SND_DEF : forall (A B : Type'), forall p : prod A B, (@snd A B p) = (@ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Axiom thm_PAIR_EQ : forall (A B : Type'), forall x : A, forall y : B, forall a : A, forall b : B, ((@pair A B x y) = (@pair A B a b)) = ((x = a) /\ (y = b)).
Axiom thm_PAIR_SURJECTIVE : forall (A B : Type'), forall p : prod A B, exists x : A, exists y : B, p = (@pair A B x y).
Axiom thm_FST : forall (A B : Type'), forall x : A, forall y : B, (@fst A B (@pair A B x y)) = x.
Axiom thm_SND : forall (A B : Type'), forall x : A, forall y : B, (@snd A B (@pair A B x y)) = y.
Axiom thm_PAIR : forall (A B : Type'), forall x : prod A B, (@pair A B (@fst A B x) (@snd A B x)) = x.
Axiom thm_pair_INDUCT : forall (A B : Type'), forall P : (prod A B) -> Prop, (forall x : A, forall y : B, P (@pair A B x y)) -> forall p : prod A B, P p.
Axiom thm_pair_RECURSION : forall (A B C : Type'), forall PAIR' : A -> B -> C, exists fn : (prod A B) -> C, forall a0 : A, forall a1 : B, (fn (@pair A B a0 a1)) = (PAIR' a0 a1).
Axiom thm_CURRY_DEF : forall (A B C : Type'), forall f : (prod A B) -> C, forall x : A, forall y : B, (CURRY A B C f x y) = (f (@pair A B x y)).
Axiom thm_UNCURRY_DEF : forall (A B C : Type'), forall f : A -> B -> C, forall x : A, forall y : B, (UNCURRY A B C f (@pair A B x y)) = (f x y).
Axiom thm_PASSOC_DEF : forall (A B C D : Type'), forall f : (prod (prod A B) C) -> D, forall x : A, forall y : B, forall z : C, (PASSOC A B C D f (@pair A (prod B C) x (@pair B C y z))) = (f (@pair (prod A B) C (@pair A B x y) z)).
Axiom thm_FORALL_PAIR_THM : forall (A B : Type'), forall P : (prod A B) -> Prop, (forall p : prod A B, P p) = (forall p1 : A, forall p2 : B, P (@pair A B p1 p2)).
Axiom thm_EXISTS_PAIR_THM : forall (A B : Type'), forall P : (prod A B) -> Prop, (exists p : prod A B, P p) = (exists p1 : A, exists p2 : B, P (@pair A B p1 p2)).
Axiom thm_LAMBDA_PAIR_THM : forall (A B C : Type'), forall t : (prod A B) -> C, (fun p : prod A B => t p) = (GABS ((prod A B) -> C) (fun f : (prod A B) -> C => forall x : A, forall y : B, GEQ C (f (@pair A B x y)) (t (@pair A B x y)))).
Axiom thm_LAMBDA_PAIR : forall (A B C : Type'), forall f : A -> B -> C, (GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, GEQ C (f' (@pair A B x y)) (f x y))) = (fun p : prod A B => f (@fst A B p) (@snd A B p)).
Axiom thm_LAMBDA_TRIPLE_THM : forall (A B C D : Type'), forall f : (prod A (prod B C)) -> D, (fun t : prod A (prod B C) => f t) = (GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, GEQ D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))).
Axiom thm_LAMBDA_TRIPLE : forall (A B C D : Type'), forall f : A -> B -> C -> D, (GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, GEQ D (f' (@pair A (prod B C) x (@pair B C y z))) (f x y z))) = (fun t : prod A (prod B C) => f (@fst A (prod B C) t) (@fst B C (@snd A (prod B C) t)) (@snd B C (@snd A (prod B C) t))).
Axiom thm_PAIRED_ETA_THM : forall (A B C D E : Type'), (forall f : (prod A B) -> C, (GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, GEQ C (f' (@pair A B x y)) (f (@pair A B x y)))) = f) /\ ((forall f : (prod A (prod B C)) -> D, (GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, GEQ D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))) = f) /\ (forall f : (prod A (prod B (prod C D))) -> E, (GABS ((prod A (prod B (prod C D))) -> E) (fun f' : (prod A (prod B (prod C D))) -> E => forall w : A, forall x : B, forall y : C, forall z : D, GEQ E (f' (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))) (f (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))))) = f)).
Axiom thm_FORALL_UNCURRY : forall (A B C : Type'), forall P : (A -> B -> C) -> Prop, (forall f : A -> B -> C, P f) = (forall f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_UNCURRY : forall (A B C : Type'), forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_CURRY : forall (A B C : Type'), forall P : ((prod A B) -> C) -> Prop, (exists f : (prod A B) -> C, P f) = (exists f : A -> B -> C, P (GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, GEQ C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_CURRY : forall (A B C : Type'), forall P : ((prod A B) -> C) -> Prop, (forall f : (prod A B) -> C, P f) = (forall f : A -> B -> C, P (GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, GEQ C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_UNPAIR_THM : forall (A B : Type'), forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_EXISTS_UNPAIR_THM : forall (A B : Type'), forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_FORALL_PAIR_FUN_THM : forall (A B C : Type'), forall P : (A -> prod B C) -> Prop, (forall f : A -> prod B C, P f) = (forall g : A -> B, forall h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_EXISTS_PAIR_FUN_THM : forall (A B C : Type'), forall P : (A -> prod B C) -> Prop, (exists f : A -> prod B C, P f) = (exists g : A -> B, exists h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_FORALL_UNPAIR_FUN_THM : forall (A B C : Type'), forall P : (A -> B) -> (A -> C) -> Prop, (forall f : A -> B, forall g : A -> C, P f g) = (forall h : A -> prod B C, P (o A (prod B C) B (@fst B C) h) (o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_UNPAIR_FUN_THM : forall (A B C : Type'), forall P : (A -> B) -> (A -> C) -> Prop, (exists f : A -> B, exists g : A -> C, P f g) = (exists h : A -> prod B C, P (o A (prod B C) B (@fst B C) h) (o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_SWAP_FUN_THM : forall (A B C : Type'), forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : B -> A -> C, P (fun a : A => fun b : B => f b a)).
Axiom thm_FORALL_PAIRED_THM : forall (A B : Type'), forall P : A -> B -> Prop, (all (GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, GEQ Prop (f (@pair A B x y)) (P x y)))) = (forall x : A, forall y : B, P x y).
Axiom thm_EXISTS_PAIRED_THM : forall (A B : Type'), forall P : A -> B -> Prop, (ex (GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, GEQ Prop (f (@pair A B x y)) (P x y)))) = (exists x : A, exists y : B, P x y).
Axiom thm_FORALL_TRIPLED_THM : forall (A B C : Type'), forall P : A -> B -> C -> Prop, (all (GABS ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, GEQ Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (forall x : A, forall y : B, forall z : C, P x y z).
Axiom thm_EXISTS_TRIPLED_THM : forall (A B C : Type'), forall P : A -> B -> C -> Prop, (ex (GABS ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, GEQ Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (exists x : A, exists y : B, exists z : C, P x y z).
Axiom thm_CHOICE_UNPAIR_THM : forall (A B : Type'), forall P : A -> B -> Prop, (@ε (prod A B) (GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, GEQ Prop (f (@pair A B x y)) (P x y)))) = (@ε (prod A B) (fun p : prod A B => P (@fst A B p) (@snd A B p))).
Axiom thm_CHOICE_PAIRED_THM : forall (A B : Type'), forall P : A -> B -> Prop, forall Q : (prod A B) -> Prop, ((exists x : A, exists y : B, P x y) /\ (forall x : A, forall y : B, (P x y) -> Q (@pair A B x y))) -> Q (@ε (prod A B) (GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, GEQ Prop (f (@pair A B x y)) (P x y)))).
Axiom thm_ONE_ONE : forall (A B : Type'), forall f : A -> B, (@ONE_ONE A B f) = (forall x1 : A, forall x2 : A, ((f x1) = (f x2)) -> x1 = x2).
Axiom thm_ONTO : forall (A B : Type'), forall f : A -> B, (@ONTO A B f) = (forall y : B, exists x : A, y = (f x)).
Axiom thm_INFINITY_AX : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Axiom thm_IND_SUC_0_EXISTS : exists f : ind -> ind, exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).
Axiom thm_NUM_REP_RULES : (NUM_REP IND_0) /\ (forall i : ind, (NUM_REP i) -> NUM_REP (IND_SUC i)).
Axiom thm_NUM_REP_CASES : forall a : ind, (NUM_REP a) = ((a = IND_0) \/ (exists i : ind, (a = (IND_SUC i)) /\ (NUM_REP i))).
Axiom thm_NUM_REP_INDUCT : forall NUM_REP' : ind -> Prop, ((NUM_REP' IND_0) /\ (forall i : ind, (NUM_REP' i) -> NUM_REP' (IND_SUC i))) -> forall a : ind, (NUM_REP a) -> NUM_REP' a.
Axiom thm_ZERO_DEF : _0 = (mk_num IND_0).
Axiom thm_SUC_DEF : forall n : num, (SUC n) = (mk_num (IND_SUC (dest_num n))).
Axiom thm_SUC_INJ : forall m : num, forall n : num, ((SUC m) = (SUC n)) = (m = n).
Axiom thm_NOT_SUC : forall n : num, ~ ((SUC n) = (NUMERAL _0)).
Axiom thm_num_INDUCTION : forall P : num -> Prop, ((P (NUMERAL _0)) /\ (forall n : num, (P n) -> P (SUC n))) -> forall n : num, P n.
Axiom thm_num_Axiom : forall (A : Type'), forall e : A, forall f : A -> num -> A, @ex1 (num -> A) (fun fn : num -> A => ((fn (NUMERAL _0)) = e) /\ (forall n : num, (fn (SUC n)) = (f (fn n) n))).
Axiom thm_num_CASES : forall m : num, (m = (NUMERAL _0)) \/ (exists n : num, m = (SUC n)).
Axiom thm_PRE : ((PRE (NUMERAL _0)) = (NUMERAL _0)) /\ (forall n : num, (PRE (SUC n)) = n).
Axiom thm_ADD : (forall n : num, (add (NUMERAL _0) n) = n) /\ (forall m : num, forall n : num, (add (SUC m) n) = (SUC (add m n))).
Axiom thm_ADD_0 : forall m : num, (add m (NUMERAL _0)) = m.
Axiom thm_ADD_SUC : forall m : num, forall n : num, (add m (SUC n)) = (SUC (add m n)).
Axiom thm_ADD_CLAUSES : (forall n : num, (add (NUMERAL _0) n) = n) /\ ((forall m : num, (add m (NUMERAL _0)) = m) /\ ((forall m : num, forall n : num, (add (SUC m) n) = (SUC (add m n))) /\ (forall m : num, forall n : num, (add m (SUC n)) = (SUC (add m n))))).
Axiom thm_ADD_SYM : forall m : num, forall n : num, (add m n) = (add n m).
Axiom thm_ADD_ASSOC : forall m : num, forall n : num, forall p : num, (add m (add n p)) = (add (add m n) p).
Axiom thm_ADD_AC : forall (n : num) (m : num) (p : num), ((add m n) = (add n m)) /\ (((add (add m n) p) = (add m (add n p))) /\ ((add m (add n p)) = (add n (add m p)))).
Axiom thm_ADD_EQ_0 : forall m : num, forall n : num, ((add m n) = (NUMERAL _0)) = ((m = (NUMERAL _0)) /\ (n = (NUMERAL _0))).
Axiom thm_EQ_ADD_LCANCEL : forall m : num, forall n : num, forall p : num, ((add m n) = (add m p)) = (n = p).
Axiom thm_EQ_ADD_RCANCEL : forall m : num, forall n : num, forall p : num, ((add m p) = (add n p)) = (m = n).
Axiom thm_EQ_ADD_LCANCEL_0 : forall m : num, forall n : num, ((add m n) = m) = (n = (NUMERAL _0)).
Axiom thm_EQ_ADD_RCANCEL_0 : forall m : num, forall n : num, ((add m n) = n) = (m = (NUMERAL _0)).
Axiom thm_BIT0 : forall n : num, (BIT0 n) = (add n n).
Axiom thm_BIT1 : forall n : num, (BIT1 n) = (SUC (add n n)).
Axiom thm_BIT0_THM : forall n : num, (NUMERAL (BIT0 n)) = (add (NUMERAL n) (NUMERAL n)).
Axiom thm_BIT1_THM : forall n : num, (NUMERAL (BIT1 n)) = (SUC (add (NUMERAL n) (NUMERAL n))).
Axiom thm_ONE : (NUMERAL (BIT1 _0)) = (SUC (NUMERAL _0)).
Axiom thm_TWO : (NUMERAL (BIT0 (BIT1 _0))) = (SUC (NUMERAL (BIT1 _0))).
Axiom thm_ADD1 : forall m : num, (SUC m) = (add m (NUMERAL (BIT1 _0))).
Axiom thm_MULT : (forall n : num, (mul (NUMERAL _0) n) = (NUMERAL _0)) /\ (forall m : num, forall n : num, (mul (SUC m) n) = (add (mul m n) n)).
Axiom thm_MULT_0 : forall m : num, (mul m (NUMERAL _0)) = (NUMERAL _0).
Axiom thm_MULT_SUC : forall m : num, forall n : num, (mul m (SUC n)) = (add m (mul m n)).
Axiom thm_MULT_CLAUSES : (forall n : num, (mul (NUMERAL _0) n) = (NUMERAL _0)) /\ ((forall m : num, (mul m (NUMERAL _0)) = (NUMERAL _0)) /\ ((forall n : num, (mul (NUMERAL (BIT1 _0)) n) = n) /\ ((forall m : num, (mul m (NUMERAL (BIT1 _0))) = m) /\ ((forall m : num, forall n : num, (mul (SUC m) n) = (add (mul m n) n)) /\ (forall m : num, forall n : num, (mul m (SUC n)) = (add m (mul m n))))))).
Axiom thm_MULT_SYM : forall m : num, forall n : num, (mul m n) = (mul n m).
Axiom thm_LEFT_ADD_DISTRIB : forall m : num, forall n : num, forall p : num, (mul m (add n p)) = (add (mul m n) (mul m p)).
Axiom thm_RIGHT_ADD_DISTRIB : forall m : num, forall n : num, forall p : num, (mul (add m n) p) = (add (mul m p) (mul n p)).
Axiom thm_MULT_ASSOC : forall m : num, forall n : num, forall p : num, (mul m (mul n p)) = (mul (mul m n) p).
Axiom thm_MULT_AC : forall (n : num) (m : num) (p : num), ((mul m n) = (mul n m)) /\ (((mul (mul m n) p) = (mul m (mul n p))) /\ ((mul m (mul n p)) = (mul n (mul m p)))).
Axiom thm_MULT_EQ_0 : forall m : num, forall n : num, ((mul m n) = (NUMERAL _0)) = ((m = (NUMERAL _0)) \/ (n = (NUMERAL _0))).
Axiom thm_EQ_MULT_LCANCEL : forall m : num, forall n : num, forall p : num, ((mul m n) = (mul m p)) = ((m = (NUMERAL _0)) \/ (n = p)).
Axiom thm_EQ_MULT_RCANCEL : forall m : num, forall n : num, forall p : num, ((mul m p) = (mul n p)) = ((m = n) \/ (p = (NUMERAL _0))).
Axiom thm_MULT_2 : forall n : num, (mul (NUMERAL (BIT0 (BIT1 _0))) n) = (add n n).
Axiom thm_MULT_EQ_1 : forall m : num, forall n : num, ((mul m n) = (NUMERAL (BIT1 _0))) = ((m = (NUMERAL (BIT1 _0))) /\ (n = (NUMERAL (BIT1 _0)))).
Axiom thm_EXP : (forall m : num, (EXP m (NUMERAL _0)) = (NUMERAL (BIT1 _0))) /\ (forall m : num, forall n : num, (EXP m (SUC n)) = (mul m (EXP m n))).
Axiom thm_EXP_EQ_0 : forall m : num, forall n : num, ((EXP m n) = (NUMERAL _0)) = ((m = (NUMERAL _0)) /\ (~ (n = (NUMERAL _0)))).
Axiom thm_EXP_EQ_1 : forall x : num, forall n : num, ((EXP x n) = (NUMERAL (BIT1 _0))) = ((x = (NUMERAL (BIT1 _0))) \/ (n = (NUMERAL _0))).
Axiom thm_EXP_ZERO : forall n : num, (EXP (NUMERAL _0) n) = (@COND num (n = (NUMERAL _0)) (NUMERAL (BIT1 _0)) (NUMERAL _0)).
Axiom thm_EXP_ADD : forall m : num, forall n : num, forall p : num, (EXP m (add n p)) = (mul (EXP m n) (EXP m p)).
Axiom thm_EXP_ONE : forall n : num, (EXP (NUMERAL (BIT1 _0)) n) = (NUMERAL (BIT1 _0)).
Axiom thm_EXP_1 : forall n : num, (EXP n (NUMERAL (BIT1 _0))) = n.
Axiom thm_EXP_2 : forall n : num, (EXP n (NUMERAL (BIT0 (BIT1 _0)))) = (mul n n).
Axiom thm_MULT_EXP : forall p : num, forall m : num, forall n : num, (EXP (mul m n) p) = (mul (EXP m p) (EXP n p)).
Axiom thm_EXP_MULT : forall m : num, forall n : num, forall p : num, (EXP m (mul n p)) = (EXP (EXP m n) p).
Axiom thm_EXP_EXP : forall x : num, forall m : num, forall n : num, (EXP (EXP x m) n) = (EXP x (mul m n)).
Axiom thm_LE : (forall m : num, (le m (NUMERAL _0)) = (m = (NUMERAL _0))) /\ (forall m : num, forall n : num, (le m (SUC n)) = ((m = (SUC n)) \/ (le m n))).
Axiom thm_LT : (forall m : num, (lt m (NUMERAL _0)) = False) /\ (forall m : num, forall n : num, (lt m (SUC n)) = ((m = n) \/ (lt m n))).
Axiom thm_GE : forall n : num, forall m : num, (ge m n) = (le n m).
Axiom thm_GT : forall n : num, forall m : num, (gt m n) = (lt n m).
Axiom thm_MAX : forall m : num, forall n : num, (MAX m n) = (@COND num (le m n) n m).
Axiom thm_MIN : forall m : num, forall n : num, (MIN m n) = (@COND num (le m n) m n).
Axiom thm_LE_SUC_LT : forall m : num, forall n : num, (le (SUC m) n) = (lt m n).
Axiom thm_LT_SUC_LE : forall m : num, forall n : num, (lt m (SUC n)) = (le m n).
Axiom thm_LE_SUC : forall m : num, forall n : num, (le (SUC m) (SUC n)) = (le m n).
Axiom thm_LT_SUC : forall m : num, forall n : num, (lt (SUC m) (SUC n)) = (lt m n).
Axiom thm_LE_0 : forall n : num, le (NUMERAL _0) n.
Axiom thm_LT_0 : forall n : num, lt (NUMERAL _0) (SUC n).
Axiom thm_LE_REFL : forall n : num, le n n.
Axiom thm_LT_REFL : forall n : num, ~ (lt n n).
Axiom thm_LT_IMP_NE : forall m : num, forall n : num, (lt m n) -> ~ (m = n).
Axiom thm_LE_ANTISYM : forall m : num, forall n : num, ((le m n) /\ (le n m)) = (m = n).
Axiom thm_LT_ANTISYM : forall m : num, forall n : num, ~ ((lt m n) /\ (lt n m)).
Axiom thm_LET_ANTISYM : forall m : num, forall n : num, ~ ((le m n) /\ (lt n m)).
Axiom thm_LTE_ANTISYM : forall m : num, forall n : num, ~ ((lt m n) /\ (le n m)).
Axiom thm_LE_TRANS : forall m : num, forall n : num, forall p : num, ((le m n) /\ (le n p)) -> le m p.
Axiom thm_LT_TRANS : forall m : num, forall n : num, forall p : num, ((lt m n) /\ (lt n p)) -> lt m p.
Axiom thm_LET_TRANS : forall m : num, forall n : num, forall p : num, ((le m n) /\ (lt n p)) -> lt m p.
Axiom thm_LTE_TRANS : forall m : num, forall n : num, forall p : num, ((lt m n) /\ (le n p)) -> lt m p.
Axiom thm_LE_CASES : forall m : num, forall n : num, (le m n) \/ (le n m).
Axiom thm_LT_CASES : forall m : num, forall n : num, (lt m n) \/ ((lt n m) \/ (m = n)).
Axiom thm_LET_CASES : forall m : num, forall n : num, (le m n) \/ (lt n m).
Axiom thm_LTE_CASES : forall m : num, forall n : num, (lt m n) \/ (le n m).
Axiom thm_LE_LT : forall m : num, forall n : num, (le m n) = ((lt m n) \/ (m = n)).
Axiom thm_LT_LE : forall m : num, forall n : num, (lt m n) = ((le m n) /\ (~ (m = n))).
Axiom thm_NOT_LE : forall m : num, forall n : num, (~ (le m n)) = (lt n m).
Axiom thm_NOT_LT : forall m : num, forall n : num, (~ (lt m n)) = (le n m).
Axiom thm_LT_IMP_LE : forall m : num, forall n : num, (lt m n) -> le m n.
Axiom thm_EQ_IMP_LE : forall m : num, forall n : num, (m = n) -> le m n.
Axiom thm_LT_NZ : forall n : num, (lt (NUMERAL _0) n) = (~ (n = (NUMERAL _0))).
Axiom thm_LE_1 : (forall n : num, (~ (n = (NUMERAL _0))) -> lt (NUMERAL _0) n) /\ ((forall n : num, (~ (n = (NUMERAL _0))) -> le (NUMERAL (BIT1 _0)) n) /\ ((forall n : num, (lt (NUMERAL _0) n) -> ~ (n = (NUMERAL _0))) /\ ((forall n : num, (lt (NUMERAL _0) n) -> le (NUMERAL (BIT1 _0)) n) /\ ((forall n : num, (le (NUMERAL (BIT1 _0)) n) -> lt (NUMERAL _0) n) /\ (forall n : num, (le (NUMERAL (BIT1 _0)) n) -> ~ (n = (NUMERAL _0))))))).
Axiom thm_LE_EXISTS : forall m : num, forall n : num, (le m n) = (exists d : num, n = (add m d)).
Axiom thm_LT_EXISTS : forall m : num, forall n : num, (lt m n) = (exists d : num, n = (add m (SUC d))).
Axiom thm_LE_ADD : forall m : num, forall n : num, le m (add m n).
Axiom thm_LE_ADDR : forall m : num, forall n : num, le n (add m n).
Axiom thm_LT_ADD : forall m : num, forall n : num, (lt m (add m n)) = (lt (NUMERAL _0) n).
Axiom thm_LT_ADDR : forall m : num, forall n : num, (lt n (add m n)) = (lt (NUMERAL _0) m).
Axiom thm_LE_ADD_LCANCEL : forall m : num, forall n : num, forall p : num, (le (add m n) (add m p)) = (le n p).
Axiom thm_LE_ADD_RCANCEL : forall m : num, forall n : num, forall p : num, (le (add m p) (add n p)) = (le m n).
Axiom thm_LT_ADD_LCANCEL : forall m : num, forall n : num, forall p : num, (lt (add m n) (add m p)) = (lt n p).
Axiom thm_LT_ADD_RCANCEL : forall m : num, forall n : num, forall p : num, (lt (add m p) (add n p)) = (lt m n).
Axiom thm_LE_ADD2 : forall m : num, forall n : num, forall p : num, forall q : num, ((le m p) /\ (le n q)) -> le (add m n) (add p q).
Axiom thm_LET_ADD2 : forall m : num, forall n : num, forall p : num, forall q : num, ((le m p) /\ (lt n q)) -> lt (add m n) (add p q).
Axiom thm_LTE_ADD2 : forall m : num, forall n : num, forall p : num, forall q : num, ((lt m p) /\ (le n q)) -> lt (add m n) (add p q).
Axiom thm_LT_ADD2 : forall m : num, forall n : num, forall p : num, forall q : num, ((lt m p) /\ (lt n q)) -> lt (add m n) (add p q).
Axiom thm_LT_MULT : forall m : num, forall n : num, (lt (NUMERAL _0) (mul m n)) = ((lt (NUMERAL _0) m) /\ (lt (NUMERAL _0) n)).
Axiom thm_LE_MULT2 : forall m : num, forall n : num, forall p : num, forall q : num, ((le m n) /\ (le p q)) -> le (mul m p) (mul n q).
Axiom thm_LT_LMULT : forall m : num, forall n : num, forall p : num, ((~ (m = (NUMERAL _0))) /\ (lt n p)) -> lt (mul m n) (mul m p).
Axiom thm_LE_MULT_LCANCEL : forall m : num, forall n : num, forall p : num, (le (mul m n) (mul m p)) = ((m = (NUMERAL _0)) \/ (le n p)).
Axiom thm_LE_MULT_RCANCEL : forall m : num, forall n : num, forall p : num, (le (mul m p) (mul n p)) = ((le m n) \/ (p = (NUMERAL _0))).
Axiom thm_LT_MULT_LCANCEL : forall m : num, forall n : num, forall p : num, (lt (mul m n) (mul m p)) = ((~ (m = (NUMERAL _0))) /\ (lt n p)).
Axiom thm_LT_MULT_RCANCEL : forall m : num, forall n : num, forall p : num, (lt (mul m p) (mul n p)) = ((lt m n) /\ (~ (p = (NUMERAL _0)))).
Axiom thm_LT_MULT2 : forall m : num, forall n : num, forall p : num, forall q : num, ((lt m n) /\ (lt p q)) -> lt (mul m p) (mul n q).
Axiom thm_LE_SQUARE_REFL : forall n : num, le n (mul n n).
Axiom thm_LT_POW2_REFL : forall n : num, lt n (EXP (NUMERAL (BIT0 (BIT1 _0))) n).
Axiom thm_WLOG_LE : forall (P : num -> num -> Prop), ((forall m : num, forall n : num, (P m n) = (P n m)) /\ (forall m : num, forall n : num, (le m n) -> P m n)) -> forall m : num, forall n : num, P m n.
Axiom thm_WLOG_LT : forall (P : num -> num -> Prop), ((forall m : num, P m m) /\ ((forall m : num, forall n : num, (P m n) = (P n m)) /\ (forall m : num, forall n : num, (lt m n) -> P m n))) -> forall m : num, forall y : num, P m y.
Axiom thm_WLOG_LE_3 : forall P : num -> num -> num -> Prop, ((forall x : num, forall y : num, forall z : num, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : num, forall y : num, forall z : num, ((le x y) /\ (le y z)) -> P x y z)) -> forall x : num, forall y : num, forall z : num, P x y z.
Axiom thm_num_WF : forall P : num -> Prop, (forall n : num, (forall m : num, (lt m n) -> P m) -> P n) -> forall n : num, P n.
Axiom thm_num_WOP : forall P : num -> Prop, (exists n : num, P n) = (exists n : num, (P n) /\ (forall m : num, (lt m n) -> ~ (P m))).
Axiom thm_num_MAX : forall P : num -> Prop, ((exists x : num, P x) /\ (exists M : num, forall x : num, (P x) -> le x M)) = (exists m : num, (P m) /\ (forall x : num, (P x) -> le x m)).
Axiom thm_LE_INDUCT : forall P : num -> num -> Prop, ((forall m : num, P m m) /\ (forall m : num, forall n : num, ((le m n) /\ (P m n)) -> P m (SUC n))) -> forall m : num, forall n : num, (le m n) -> P m n.
Axiom thm_num_INDUCTION_DOWN : forall P : num -> Prop, forall m : num, ((forall n : num, (le m n) -> P n) /\ (forall n : num, ((lt n m) /\ (P (add n (NUMERAL (BIT1 _0))))) -> P n)) -> forall n : num, P n.
Axiom thm_EVEN : ((EVEN (NUMERAL _0)) = True) /\ (forall n : num, (EVEN (SUC n)) = (~ (EVEN n))).
Axiom thm_ODD : ((ODD (NUMERAL _0)) = False) /\ (forall n : num, (ODD (SUC n)) = (~ (ODD n))).
Axiom thm_NOT_EVEN : forall n : num, (~ (EVEN n)) = (ODD n).
Axiom thm_NOT_ODD : forall n : num, (~ (ODD n)) = (EVEN n).
Axiom thm_EVEN_OR_ODD : forall n : num, (EVEN n) \/ (ODD n).
Axiom thm_EVEN_AND_ODD : forall n : num, ~ ((EVEN n) /\ (ODD n)).
Axiom thm_EVEN_ADD : forall m : num, forall n : num, (EVEN (add m n)) = ((EVEN m) = (EVEN n)).
Axiom thm_EVEN_MULT : forall m : num, forall n : num, (EVEN (mul m n)) = ((EVEN m) \/ (EVEN n)).
Axiom thm_EVEN_EXP : forall m : num, forall n : num, (EVEN (EXP m n)) = ((EVEN m) /\ (~ (n = (NUMERAL _0)))).
Axiom thm_ODD_ADD : forall m : num, forall n : num, (ODD (add m n)) = (~ ((ODD m) = (ODD n))).
Axiom thm_ODD_MULT : forall m : num, forall n : num, (ODD (mul m n)) = ((ODD m) /\ (ODD n)).
Axiom thm_ODD_EXP : forall m : num, forall n : num, (ODD (EXP m n)) = ((ODD m) \/ (n = (NUMERAL _0))).
Axiom thm_EVEN_DOUBLE : forall n : num, EVEN (mul (NUMERAL (BIT0 (BIT1 _0))) n).
Axiom thm_ODD_DOUBLE : forall n : num, ODD (SUC (mul (NUMERAL (BIT0 (BIT1 _0))) n)).
Axiom thm_EVEN_EXISTS_LEMMA : forall n : num, ((EVEN n) -> exists m : num, n = (mul (NUMERAL (BIT0 (BIT1 _0))) m)) /\ ((~ (EVEN n)) -> exists m : num, n = (SUC (mul (NUMERAL (BIT0 (BIT1 _0))) m))).
Axiom thm_EVEN_EXISTS : forall n : num, (EVEN n) = (exists m : num, n = (mul (NUMERAL (BIT0 (BIT1 _0))) m)).
Axiom thm_ODD_EXISTS : forall n : num, (ODD n) = (exists m : num, n = (SUC (mul (NUMERAL (BIT0 (BIT1 _0))) m))).
Axiom thm_EVEN_ODD_DECOMPOSITION : forall n : num, (exists k : num, exists m : num, (ODD m) /\ (n = (mul (EXP (NUMERAL (BIT0 (BIT1 _0))) k) m))) = (~ (n = (NUMERAL _0))).
Axiom thm_SUB : (forall m : num, (minus m (NUMERAL _0)) = m) /\ (forall m : num, forall n : num, (minus m (SUC n)) = (PRE (minus m n))).
Axiom thm_SUB_0 : forall m : num, ((minus (NUMERAL _0) m) = (NUMERAL _0)) /\ ((minus m (NUMERAL _0)) = m).
Axiom thm_SUB_PRESUC : forall m : num, forall n : num, (PRE (minus (SUC m) n)) = (minus m n).
Axiom thm_SUB_SUC : forall m : num, forall n : num, (minus (SUC m) (SUC n)) = (minus m n).
Axiom thm_SUB_REFL : forall n : num, (minus n n) = (NUMERAL _0).
Axiom thm_ADD_SUB : forall m : num, forall n : num, (minus (add m n) n) = m.
Axiom thm_ADD_SUB2 : forall m : num, forall n : num, (minus (add m n) m) = n.
Axiom thm_SUB_EQ_0 : forall m : num, forall n : num, ((minus m n) = (NUMERAL _0)) = (le m n).
Axiom thm_ADD_SUBR2 : forall m : num, forall n : num, (minus m (add m n)) = (NUMERAL _0).
Axiom thm_ADD_SUBR : forall m : num, forall n : num, (minus n (add m n)) = (NUMERAL _0).
Axiom thm_SUB_ADD : forall m : num, forall n : num, (le n m) -> (add (minus m n) n) = m.
Axiom thm_SUB_ADD_LCANCEL : forall m : num, forall n : num, forall p : num, (minus (add m n) (add m p)) = (minus n p).
Axiom thm_SUB_ADD_RCANCEL : forall m : num, forall n : num, forall p : num, (minus (add m p) (add n p)) = (minus m n).
Axiom thm_LEFT_SUB_DISTRIB : forall m : num, forall n : num, forall p : num, (mul m (minus n p)) = (minus (mul m n) (mul m p)).
Axiom thm_RIGHT_SUB_DISTRIB : forall m : num, forall n : num, forall p : num, (mul (minus m n) p) = (minus (mul m p) (mul n p)).
Axiom thm_SUC_SUB1 : forall n : num, (minus (SUC n) (NUMERAL (BIT1 _0))) = n.
Axiom thm_EVEN_SUB : forall m : num, forall n : num, (EVEN (minus m n)) = ((le m n) \/ ((EVEN m) = (EVEN n))).
Axiom thm_ODD_SUB : forall m : num, forall n : num, (ODD (minus m n)) = ((lt n m) /\ (~ ((ODD m) = (ODD n)))).
Axiom thm_FACT : ((FACT (NUMERAL _0)) = (NUMERAL (BIT1 _0))) /\ (forall n : num, (FACT (SUC n)) = (mul (SUC n) (FACT n))).
Axiom thm_FACT_LT : forall n : num, lt (NUMERAL _0) (FACT n).
Axiom thm_FACT_LE : forall n : num, le (NUMERAL (BIT1 _0)) (FACT n).
Axiom thm_FACT_NZ : forall n : num, ~ ((FACT n) = (NUMERAL _0)).
Axiom thm_FACT_MONO : forall m : num, forall n : num, (le m n) -> le (FACT m) (FACT n).
Axiom thm_EXP_LT_0 : forall n : num, forall x : num, (lt (NUMERAL _0) (EXP x n)) = ((~ (x = (NUMERAL _0))) \/ (n = (NUMERAL _0))).
Axiom thm_LT_EXP : forall x : num, forall m : num, forall n : num, (lt (EXP x m) (EXP x n)) = (((le (NUMERAL (BIT0 (BIT1 _0))) x) /\ (lt m n)) \/ ((x = (NUMERAL _0)) /\ ((~ (m = (NUMERAL _0))) /\ (n = (NUMERAL _0))))).
Axiom thm_LE_EXP : forall x : num, forall m : num, forall n : num, (le (EXP x m) (EXP x n)) = (@COND Prop (x = (NUMERAL _0)) ((m = (NUMERAL _0)) -> n = (NUMERAL _0)) ((x = (NUMERAL (BIT1 _0))) \/ (le m n))).
Axiom thm_EQ_EXP : forall x : num, forall m : num, forall n : num, ((EXP x m) = (EXP x n)) = (@COND Prop (x = (NUMERAL _0)) ((m = (NUMERAL _0)) = (n = (NUMERAL _0))) ((x = (NUMERAL (BIT1 _0))) \/ (m = n))).
Axiom thm_EXP_MONO_LE_IMP : forall x : num, forall y : num, forall n : num, (le x y) -> le (EXP x n) (EXP y n).
Axiom thm_EXP_MONO_LT_IMP : forall x : num, forall y : num, forall n : num, ((lt x y) /\ (~ (n = (NUMERAL _0)))) -> lt (EXP x n) (EXP y n).
Axiom thm_EXP_MONO_LE : forall x : num, forall y : num, forall n : num, (le (EXP x n) (EXP y n)) = ((le x y) \/ (n = (NUMERAL _0))).
Axiom thm_EXP_MONO_LT : forall x : num, forall y : num, forall n : num, (lt (EXP x n) (EXP y n)) = ((lt x y) /\ (~ (n = (NUMERAL _0)))).
Axiom thm_EXP_MONO_EQ : forall x : num, forall y : num, forall n : num, ((EXP x n) = (EXP y n)) = ((x = y) \/ (n = (NUMERAL _0))).
Axiom thm_DIVMOD_EXIST : forall m : num, forall n : num, (~ (n = (NUMERAL _0))) -> exists q : num, exists r : num, (m = (add (mul q n) r)) /\ (lt r n).
Axiom thm_DIVMOD_EXIST_0 : forall m : num, forall n : num, exists q : num, exists r : num, @COND Prop (n = (NUMERAL _0)) ((q = (NUMERAL _0)) /\ (r = m)) ((m = (add (mul q n) r)) /\ (lt r n)).
Axiom thm_DIVISION : forall m : num, forall n : num, (~ (n = (NUMERAL _0))) -> (m = (add (mul (DIV m n) n) (MOD m n))) /\ (lt (MOD m n) n).
Axiom thm_DIV_ZERO : forall n : num, (DIV n (NUMERAL _0)) = (NUMERAL _0).
Axiom thm_MOD_ZERO : forall n : num, (MOD n (NUMERAL _0)) = n.
Axiom thm_DIVISION_SIMP : (forall m : num, forall n : num, (add (mul (DIV m n) n) (MOD m n)) = m) /\ (forall m : num, forall n : num, (add (mul n (DIV m n)) (MOD m n)) = m).
Axiom thm_EQ_DIVMOD : forall p : num, forall m : num, forall n : num, (((DIV m p) = (DIV n p)) /\ ((MOD m p) = (MOD n p))) = (m = n).
Axiom thm_MOD_LT_EQ : forall m : num, forall n : num, (lt (MOD m n) n) = (~ (n = (NUMERAL _0))).
Axiom thm_MOD_LT_EQ_LT : forall m : num, forall n : num, (lt (MOD m n) n) = (lt (NUMERAL _0) n).
Axiom thm_DIVMOD_UNIQ_LEMMA : forall m : num, forall n : num, forall q1 : num, forall r1 : num, forall q2 : num, forall r2 : num, (((m = (add (mul q1 n) r1)) /\ (lt r1 n)) /\ ((m = (add (mul q2 n) r2)) /\ (lt r2 n))) -> (q1 = q2) /\ (r1 = r2).
Axiom thm_DIVMOD_UNIQ : forall m : num, forall n : num, forall q : num, forall r : num, ((m = (add (mul q n) r)) /\ (lt r n)) -> ((DIV m n) = q) /\ ((MOD m n) = r).
Axiom thm_MOD_UNIQ : forall m : num, forall n : num, forall q : num, forall r : num, ((m = (add (mul q n) r)) /\ (lt r n)) -> (MOD m n) = r.
Axiom thm_DIV_UNIQ : forall m : num, forall n : num, forall q : num, forall r : num, ((m = (add (mul q n) r)) /\ (lt r n)) -> (DIV m n) = q.
Axiom thm_MOD_0 : forall n : num, (MOD (NUMERAL _0) n) = (NUMERAL _0).
Axiom thm_DIV_0 : forall n : num, (DIV (NUMERAL _0) n) = (NUMERAL _0).
Axiom thm_MOD_MULT : forall m : num, forall n : num, (MOD (mul m n) m) = (NUMERAL _0).
Axiom thm_DIV_MULT : forall m : num, forall n : num, (~ (m = (NUMERAL _0))) -> (DIV (mul m n) m) = n.
Axiom thm_MOD_LT : forall m : num, forall n : num, (lt m n) -> (MOD m n) = m.
Axiom thm_MOD_EQ_SELF : forall m : num, forall n : num, ((MOD m n) = m) = ((n = (NUMERAL _0)) \/ (lt m n)).
Axiom thm_MOD_CASES : forall n : num, forall p : num, (lt n (mul (NUMERAL (BIT0 (BIT1 _0))) p)) -> (MOD n p) = (@COND num (lt n p) n (minus n p)).
Axiom thm_MOD_ADD_CASES : forall m : num, forall n : num, forall p : num, ((lt m p) /\ (lt n p)) -> (MOD (add m n) p) = (@COND num (lt (add m n) p) (add m n) (minus (add m n) p)).
Axiom thm_MOD_EQ : forall m : num, forall n : num, forall p : num, forall q : num, (m = (add n (mul q p))) -> (MOD m p) = (MOD n p).
Axiom thm_DIV_LE : forall m : num, forall n : num, le (DIV m n) m.
Axiom thm_DIV_MUL_LE : forall m : num, forall n : num, le (mul n (DIV m n)) m.
Axiom thm_MOD_LE_TWICE : forall m : num, forall n : num, ((lt (NUMERAL _0) m) /\ (le m n)) -> le (mul (NUMERAL (BIT0 (BIT1 _0))) (MOD n m)) n.
Axiom thm_MOD_1 : forall n : num, (MOD n (NUMERAL (BIT1 _0))) = (NUMERAL _0).
Axiom thm_DIV_1 : forall n : num, (DIV n (NUMERAL (BIT1 _0))) = n.
Axiom thm_DIV_LT : forall m : num, forall n : num, (lt m n) -> (DIV m n) = (NUMERAL _0).
Axiom thm_MOD_MOD : forall m : num, forall n : num, forall p : num, (MOD (MOD m (mul n p)) n) = (MOD m n).
Axiom thm_MOD_MOD_REFL : forall m : num, forall n : num, (MOD (MOD m n) n) = (MOD m n).
Axiom thm_MOD_MOD_LE : forall m : num, forall n : num, forall p : num, ((~ (n = (NUMERAL _0))) /\ (le n p)) -> (MOD (MOD m n) p) = (MOD m n).
Axiom thm_MOD_EVEN_2 : forall m : num, forall n : num, (EVEN n) -> (MOD (MOD m n) (NUMERAL (BIT0 (BIT1 _0)))) = (MOD m (NUMERAL (BIT0 (BIT1 _0)))).
Axiom thm_DIV_MULT2 : forall m : num, forall n : num, forall p : num, (~ (m = (NUMERAL _0))) -> (DIV (mul m n) (mul m p)) = (DIV n p).
Axiom thm_MOD_MULT2 : forall m : num, forall n : num, forall p : num, (MOD (mul m n) (mul m p)) = (mul m (MOD n p)).
Axiom thm_MOD_EXISTS : forall m : num, forall n : num, (exists q : num, m = (mul n q)) = (@COND Prop (n = (NUMERAL _0)) (m = (NUMERAL _0)) ((MOD m n) = (NUMERAL _0))).
Axiom thm_LE_RDIV_EQ : forall a : num, forall b : num, forall n : num, (~ (a = (NUMERAL _0))) -> (le n (DIV b a)) = (le (mul a n) b).
Axiom thm_RDIV_LT_EQ : forall a : num, forall b : num, forall n : num, (~ (a = (NUMERAL _0))) -> (lt (DIV b a) n) = (lt b (mul a n)).
Axiom thm_LE_LDIV_EQ : forall a : num, forall b : num, forall n : num, (~ (a = (NUMERAL _0))) -> (le (DIV b a) n) = (lt b (mul a (add n (NUMERAL (BIT1 _0))))).
Axiom thm_LDIV_LT_EQ : forall a : num, forall b : num, forall n : num, (~ (a = (NUMERAL _0))) -> (lt n (DIV b a)) = (le (mul a (add n (NUMERAL (BIT1 _0)))) b).
Axiom thm_LE_LDIV : forall a : num, forall b : num, forall n : num, ((~ (a = (NUMERAL _0))) /\ (le b (mul a n))) -> le (DIV b a) n.
Axiom thm_DIV_MONO : forall m : num, forall n : num, forall p : num, (le m n) -> le (DIV m p) (DIV n p).
Axiom thm_DIV_MONO_LT : forall m : num, forall n : num, forall p : num, ((~ (p = (NUMERAL _0))) /\ (le (add m p) n)) -> lt (DIV m p) (DIV n p).
Axiom thm_DIV_EQ_0 : forall m : num, forall n : num, (~ (n = (NUMERAL _0))) -> ((DIV m n) = (NUMERAL _0)) = (lt m n).
Axiom thm_MOD_DIV_EQ_0 : forall m : num, forall n : num, (~ (n = (NUMERAL _0))) -> (DIV (MOD m n) n) = (NUMERAL _0).
Axiom thm_MOD_EQ_0 : forall m : num, forall n : num, ((MOD m n) = (NUMERAL _0)) = (exists q : num, m = (mul q n)).
Axiom thm_DIV_EQ_SELF : forall m : num, forall n : num, ((DIV m n) = m) = ((m = (NUMERAL _0)) \/ (n = (NUMERAL (BIT1 _0)))).
Axiom thm_MOD_REFL : forall n : num, (MOD n n) = (NUMERAL _0).
Axiom thm_EVEN_MOD : forall n : num, (EVEN n) = ((MOD n (NUMERAL (BIT0 (BIT1 _0)))) = (NUMERAL _0)).
Axiom thm_ODD_MOD : forall n : num, (ODD n) = ((MOD n (NUMERAL (BIT0 (BIT1 _0)))) = (NUMERAL (BIT1 _0))).
Axiom thm_MOD_2_CASES : forall n : num, (MOD n (NUMERAL (BIT0 (BIT1 _0)))) = (@COND num (EVEN n) (NUMERAL _0) (NUMERAL (BIT1 _0))).
Axiom thm_EVEN_MOD_EVEN : forall m : num, forall n : num, (EVEN n) -> (EVEN (MOD m n)) = (EVEN m).
Axiom thm_ODD_MOD_EVEN : forall m : num, forall n : num, (EVEN n) -> (ODD (MOD m n)) = (ODD m).
Axiom thm_HALF_DOUBLE : (forall n : num, (DIV (mul (NUMERAL (BIT0 (BIT1 _0))) n) (NUMERAL (BIT0 (BIT1 _0)))) = n) /\ (forall n : num, (DIV (mul n (NUMERAL (BIT0 (BIT1 _0)))) (NUMERAL (BIT0 (BIT1 _0)))) = n).
Axiom thm_DOUBLE_HALF : (forall n : num, (EVEN n) -> (mul (NUMERAL (BIT0 (BIT1 _0))) (DIV n (NUMERAL (BIT0 (BIT1 _0))))) = n) /\ (forall n : num, (EVEN n) -> (mul (DIV n (NUMERAL (BIT0 (BIT1 _0)))) (NUMERAL (BIT0 (BIT1 _0)))) = n).
Axiom thm_MOD_MULT_RMOD : forall m : num, forall n : num, forall p : num, (MOD (mul m (MOD p n)) n) = (MOD (mul m p) n).
Axiom thm_MOD_MULT_LMOD : forall m : num, forall n : num, forall p : num, (MOD (mul (MOD m n) p) n) = (MOD (mul m p) n).
Axiom thm_MOD_MULT_MOD2 : forall m : num, forall n : num, forall p : num, (MOD (mul (MOD m n) (MOD p n)) n) = (MOD (mul m p) n).
Axiom thm_MOD_EXP_MOD : forall m : num, forall n : num, forall p : num, (MOD (EXP (MOD m n) p) n) = (MOD (EXP m p) n).
Axiom thm_MOD_MULT_ADD : (forall m : num, forall n : num, forall p : num, (MOD (add (mul m n) p) n) = (MOD p n)) /\ ((forall m : num, forall n : num, forall p : num, (MOD (add (mul n m) p) n) = (MOD p n)) /\ ((forall m : num, forall n : num, forall p : num, (MOD (add p (mul m n)) n) = (MOD p n)) /\ (forall m : num, forall n : num, forall p : num, (MOD (add p (mul n m)) n) = (MOD p n)))).
Axiom thm_DIV_MULT_ADD : (forall a : num, forall b : num, forall n : num, (~ (n = (NUMERAL _0))) -> (DIV (add (mul a n) b) n) = (add a (DIV b n))) /\ ((forall a : num, forall b : num, forall n : num, (~ (n = (NUMERAL _0))) -> (DIV (add (mul n a) b) n) = (add a (DIV b n))) /\ ((forall a : num, forall b : num, forall n : num, (~ (n = (NUMERAL _0))) -> (DIV (add b (mul a n)) n) = (add (DIV b n) a)) /\ (forall a : num, forall b : num, forall n : num, (~ (n = (NUMERAL _0))) -> (DIV (add b (mul n a)) n) = (add (DIV b n) a)))).
Axiom thm_MOD_ADD_MOD : forall a : num, forall b : num, forall n : num, (MOD (add (MOD a n) (MOD b n)) n) = (MOD (add a b) n).
Axiom thm_DIV_ADD_MOD : forall a : num, forall b : num, forall n : num, (~ (n = (NUMERAL _0))) -> ((MOD (add a b) n) = (add (MOD a n) (MOD b n))) = ((DIV (add a b) n) = (add (DIV a n) (DIV b n))).
Axiom thm_MOD_ADD_EQ_EQ : forall n : num, forall x : num, forall y : num, ((MOD (add x y) n) = (add (MOD x n) (MOD y n))) = ((n = (NUMERAL _0)) \/ (lt (add (MOD x n) (MOD y n)) n)).
Axiom thm_DIV_ADD_EQ_EQ : forall n : num, forall x : num, forall y : num, ((DIV (add x y) n) = (add (DIV x n) (DIV y n))) = ((n = (NUMERAL _0)) \/ (lt (add (MOD x n) (MOD y n)) n)).
Axiom thm_DIV_ADD_EQ : forall n : num, forall x : num, forall y : num, (lt (add (MOD x n) (MOD y n)) n) -> (DIV (add x y) n) = (add (DIV x n) (DIV y n)).
Axiom thm_MOD_ADD_EQ : forall n : num, forall x : num, forall y : num, (lt (add (MOD x n) (MOD y n)) n) -> (MOD (add x y) n) = (add (MOD x n) (MOD y n)).
Axiom thm_DIV_REFL : forall n : num, (~ (n = (NUMERAL _0))) -> (DIV n n) = (NUMERAL (BIT1 _0)).
Axiom thm_MOD_LE : forall m : num, forall n : num, le (MOD m n) m.
Axiom thm_DIV_MONO2 : forall m : num, forall n : num, forall p : num, ((~ (p = (NUMERAL _0))) /\ (le p m)) -> le (DIV n m) (DIV n p).
Axiom thm_DIV_LE_EXCLUSION : forall a : num, forall b : num, forall c : num, forall d : num, ((~ (b = (NUMERAL _0))) /\ (lt (mul b c) (mul (add a (NUMERAL (BIT1 _0))) d))) -> le (DIV c d) (DIV a b).
Axiom thm_DIV_EQ_EXCLUSION : forall a : num, forall b : num, forall c : num, forall d : num, ((lt (mul b c) (mul (add a (NUMERAL (BIT1 _0))) d)) /\ (lt (mul a d) (mul (add c (NUMERAL (BIT1 _0))) b))) -> (DIV a b) = (DIV c d).
Axiom thm_MULT_DIV_LE : forall m : num, forall n : num, forall p : num, le (mul m (DIV n p)) (DIV (mul m n) p).
Axiom thm_DIV_DIV : forall m : num, forall n : num, forall p : num, (DIV (DIV m n) p) = (DIV m (mul n p)).
Axiom thm_DIV_MOD : forall m : num, forall n : num, forall p : num, (MOD (DIV m n) p) = (DIV (MOD m (mul n p)) n).
Axiom thm_MOD_MULT_MOD : forall m : num, forall n : num, forall p : num, (MOD m (mul n p)) = (add (mul n (MOD (DIV m n) p)) (MOD m n)).
Axiom thm_MOD_MOD_EXP_MIN : forall x : num, forall p : num, forall m : num, forall n : num, (MOD (MOD x (EXP p m)) (EXP p n)) = (MOD x (EXP p (MIN m n))).
Axiom thm_MOD_EXP : forall m : num, forall n : num, forall p : num, (~ (m = (NUMERAL _0))) -> (MOD (EXP m n) (EXP m p)) = (@COND num ((le p n) \/ (m = (NUMERAL (BIT1 _0)))) (NUMERAL _0) (EXP m n)).
Axiom thm_DIV_EXP : forall m : num, forall n : num, forall p : num, (~ (m = (NUMERAL _0))) -> (DIV (EXP m n) (EXP m p)) = (@COND num (le p n) (EXP m (minus n p)) (@COND num (m = (NUMERAL (BIT1 _0))) (NUMERAL (BIT1 _0)) (NUMERAL _0))).
Axiom thm_FORALL_LT_MOD_THM : forall P : num -> Prop, forall n : num, (forall a : num, (lt a n) -> P a) = ((n = (NUMERAL _0)) \/ (forall a : num, P (MOD a n))).
Axiom thm_FORALL_MOD_THM : forall P : num -> Prop, forall n : num, (~ (n = (NUMERAL _0))) -> (forall a : num, P (MOD a n)) = (forall a : num, (lt a n) -> P a).
Axiom thm_EXISTS_LT_MOD_THM : forall P : num -> Prop, forall n : num, (exists a : num, (lt a n) /\ (P a)) = ((~ (n = (NUMERAL _0))) /\ (exists a : num, P (MOD a n))).
Axiom thm_EXISTS_MOD_THM : forall P : num -> Prop, forall n : num, (~ (n = (NUMERAL _0))) -> (exists a : num, P (MOD a n)) = (exists a : num, (lt a n) /\ (P a)).
Axiom thm_PRE_ELIM_THM : forall (n : num) (P : num -> Prop), (P (PRE n)) = (forall m : num, ((n = (SUC m)) \/ ((m = (NUMERAL _0)) /\ (n = (NUMERAL _0)))) -> P m).
Axiom thm_SUB_ELIM_THM : forall (a : num) (b : num) (P : num -> Prop), (P (minus a b)) = (forall d : num, ((a = (add b d)) \/ ((lt a b) /\ (d = (NUMERAL _0)))) -> P d).
Axiom thm_DIVMOD_ELIM_THM : forall (m : num) (n : num) (P : num -> num -> Prop), (P (DIV m n) (MOD m n)) = (forall q : num, forall r : num, (((n = (NUMERAL _0)) /\ ((q = (NUMERAL _0)) /\ (r = m))) \/ ((m = (add (mul q n) r)) /\ (lt r n))) -> P q r).
Axiom thm_minimal : forall P : num -> Prop, (minimal P) = (@ε num (fun n : num => (P n) /\ (forall m : num, (lt m n) -> ~ (P m)))).
Axiom thm_MINIMAL : forall P : num -> Prop, (exists n : num, P n) = ((P (minimal P)) /\ (forall m : num, (lt m (minimal P)) -> ~ (P m))).
Axiom thm_MINIMAL_UNIQUE : forall P : num -> Prop, forall n : num, ((P n) /\ (forall m : num, (lt m n) -> ~ (P m))) -> (minimal P) = n.
Axiom thm_LE_MINIMAL : forall P : num -> Prop, forall n : num, (exists r : num, P r) -> (le n (minimal P)) = (forall i : num, (P i) -> le n i).
Axiom thm_MINIMAL_LE : forall P : num -> Prop, forall n : num, (exists r : num, P r) -> (le (minimal P) n) = (exists i : num, (le i n) /\ (P i)).
Axiom thm_MINIMAL_UBOUND : forall P : num -> Prop, forall n : num, (P n) -> le (minimal P) n.
Axiom thm_MINIMAL_LBOUND : forall P : num -> Prop, forall n : num, ((exists r : num, P r) /\ (forall m : num, (lt m n) -> ~ (P m))) -> le n (minimal P).
Axiom thm_MINIMAL_MONO : forall P : num -> Prop, forall Q : num -> Prop, ((exists n : num, P n) /\ (forall n : num, (P n) -> Q n)) -> le (minimal Q) (minimal P).
Axiom thm_TRANSITIVE_STEPWISE_LT_EQ : forall R' : num -> num -> Prop, (forall x : num, forall y : num, forall z : num, ((R' x y) /\ (R' y z)) -> R' x z) -> (forall m : num, forall n : num, (lt m n) -> R' m n) = (forall n : num, R' n (SUC n)).
Axiom thm_TRANSITIVE_STEPWISE_LT : forall R' : num -> num -> Prop, ((forall x : num, forall y : num, forall z : num, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : num, R' n (SUC n))) -> forall m : num, forall n : num, (lt m n) -> R' m n.
Axiom thm_TRANSITIVE_STEPWISE_LE_EQ : forall R' : num -> num -> Prop, ((forall x : num, R' x x) /\ (forall x : num, forall y : num, forall z : num, ((R' x y) /\ (R' y z)) -> R' x z)) -> (forall m : num, forall n : num, (le m n) -> R' m n) = (forall n : num, R' n (SUC n)).
Axiom thm_TRANSITIVE_STEPWISE_LE : forall R' : num -> num -> Prop, ((forall x : num, R' x x) /\ ((forall x : num, forall y : num, forall z : num, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : num, R' n (SUC n)))) -> forall m : num, forall n : num, (le m n) -> R' m n.
Axiom thm_DEPENDENT_CHOICE_FIXED : forall (A : Type'), forall P : num -> A -> Prop, forall R' : num -> A -> A -> Prop, forall a : A, ((P (NUMERAL _0) a) /\ (forall n : num, forall x : A, (P n x) -> exists y : A, (P (SUC n) y) /\ (R' n x y))) -> exists f : num -> A, ((f (NUMERAL _0)) = a) /\ ((forall n : num, P n (f n)) /\ (forall n : num, R' n (f n) (f (SUC n)))).
Axiom thm_DEPENDENT_CHOICE : forall (A : Type'), forall P : num -> A -> Prop, forall R' : num -> A -> A -> Prop, ((exists a : A, P (NUMERAL _0) a) /\ (forall n : num, forall x : A, (P n x) -> exists y : A, (P (SUC n) y) /\ (R' n x y))) -> exists f : num -> A, (forall n : num, P n (f n)) /\ (forall n : num, R' n (f n) (f (SUC n))).
Axiom thm_WF : forall (A : Type'), forall lt2 : A -> A -> Prop, (WF A lt2) = (forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y))).
Axiom thm_WF_EQ : forall (A : Type') (lt2 : A -> A -> Prop), (WF A lt2) = (forall P : A -> Prop, (exists x : A, P x) = (exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y)))).
Axiom thm_WF_IND : forall (A : Type') (lt2 : A -> A -> Prop), (WF A lt2) = (forall P : A -> Prop, (forall x : A, (forall y : A, (lt2 y x) -> P y) -> P x) -> forall x : A, P x).
Axiom thm_WF_DCHAIN : forall (A : Type') (lt2 : A -> A -> Prop), (WF A lt2) = (~ (exists s : num -> A, forall n : num, lt2 (s (SUC n)) (s n))).
Axiom thm_WF_DHAIN_TRANSITIVE : forall (A : Type'), forall lt2 : A -> A -> Prop, (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) -> (WF A lt2) = (~ (exists s : num -> A, forall i : num, forall j : num, (lt i j) -> lt2 (s j) (s i))).
Axiom thm_WF_UREC : forall (A B : Type') (lt2 : A -> A -> Prop), (WF A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> B, forall g : A -> B, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g.
Axiom thm_WF_UREC_WF : forall (A : Type') (lt2 : A -> A -> Prop), (forall H : (A -> Prop) -> A -> Prop, (forall f : A -> Prop, forall g : A -> Prop, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> Prop, forall g : A -> Prop, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g) -> WF A lt2.
Axiom thm_WF_REC_INVARIANT : forall (A B : Type') (lt2 : A -> A -> Prop), (WF A lt2) -> forall H : (A -> B) -> A -> B, forall S' : A -> B -> Prop, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> ((f z) = (g z)) /\ (S' z (f z))) -> ((H f x) = (H g x)) /\ (S' x (H f x))) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC : forall (A B : Type') (lt2 : A -> A -> Prop), (WF A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC_WF : forall (A : Type') (lt2 : A -> A -> Prop), (forall H : (A -> num) -> A -> num, (forall f : A -> num, forall g : A -> num, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> num, forall x : A, (f x) = (H f x)) -> WF A lt2.
Axiom thm_WF_EREC : forall (A B : Type') (lt2 : A -> A -> Prop), (WF A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> @ex1 (A -> B) (fun f : A -> B => forall x : A, (f x) = (H f x)).
Axiom thm_WF_REC_EXISTS : forall (A B : Type') (lt2 : A -> A -> Prop), (WF A lt2) -> forall P : (A -> B) -> A -> B -> Prop, ((forall f : A -> B, forall g : A -> B, forall x : A, forall y : B, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (P f x y) = (P g x y)) /\ (forall f : A -> B, forall x : A, (forall z : A, (lt2 z x) -> P f z (f z)) -> exists y : B, P f x y)) -> exists f : A -> B, forall x : A, P f x (f x).
Axiom thm_WF_SUBSET : forall (A : Type'), forall lt2 : A -> A -> Prop, forall lt3 : A -> A -> Prop, ((forall x : A, forall y : A, (lt2 x y) -> lt3 x y) /\ (WF A lt3)) -> WF A lt2.
Axiom thm_WF_RESTRICT : forall (A : Type'), forall lt2 : A -> A -> Prop, forall P : A -> Prop, (WF A lt2) -> WF A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (lt2 x y))).
Axiom thm_WF_MEASURE_GEN : forall (A B : Type'), forall lt2 : B -> B -> Prop, forall m : A -> B, (WF B lt2) -> WF A (fun x : A => fun x' : A => lt2 (m x) (m x')).
Axiom thm_WF_LEX_DEPENDENT : forall (A B : Type'), forall R' : A -> A -> Prop, forall S' : A -> B -> B -> Prop, ((WF A R') /\ (forall a : A, WF B (S' a))) -> WF (prod A B) (GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, GEQ ((prod A B) -> Prop) (f (@pair A B r1 s1)) (GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, GEQ Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' r1 s1 s2))))))).
Axiom thm_WF_LEX : forall (A B : Type'), forall R' : A -> A -> Prop, forall S' : B -> B -> Prop, ((WF A R') /\ (WF B S')) -> WF (prod A B) (GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, GEQ ((prod A B) -> Prop) (f (@pair A B r1 s1)) (GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, GEQ Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' s1 s2))))))).
Axiom thm_WF_POINTWISE : forall (A B : Type') (lt2 : A -> A -> Prop) (lt3 : B -> B -> Prop), ((WF A lt2) /\ (WF B lt3)) -> WF (prod A B) (GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall x1 : A, forall y1 : B, GEQ ((prod A B) -> Prop) (f (@pair A B x1 y1)) (GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall x2 : A, forall y2 : B, GEQ Prop (f' (@pair A B x2 y2)) ((lt2 x1 x2) /\ (lt3 y1 y2)))))).
Axiom thm_WF_num : WF num lt.
Axiom thm_WF_REC_num : forall (A : Type'), forall H : (num -> A) -> num -> A, (forall f : num -> A, forall g : num -> A, forall n : num, (forall m : num, (lt m n) -> (f m) = (g m)) -> (H f n) = (H g n)) -> exists f : num -> A, forall n : num, (f n) = (H f n).
Axiom thm_MEASURE : forall (A : Type'), forall m : A -> num, (MEASURE A m) = (fun x : A => fun y : A => lt (m x) (m y)).
Axiom thm_WF_MEASURE : forall (A : Type'), forall m : A -> num, WF A (MEASURE A m).
Axiom thm_MEASURE_LE : forall (A : Type') (a : A) (b : A), forall m : A -> num, (forall y : A, (MEASURE A m y a) -> MEASURE A m y b) = (le (m a) (m b)).
Axiom thm_WF_ANTISYM : forall (A : Type'), forall lt2 : A -> A -> Prop, forall x : A, forall y : A, (WF A lt2) -> ~ ((lt2 x y) /\ (lt2 y x)).
Axiom thm_WF_REFL : forall (A : Type') (lt2 : A -> A -> Prop), forall x : A, (WF A lt2) -> ~ (lt2 x x).
Axiom thm_WF_FALSE : forall (A : Type'), WF A (fun x : A => fun y : A => False).
Axiom thm_MINIMAL_BAD_SEQUENCE : forall (A : Type'), forall lt2 : A -> A -> Prop, forall bad : (num -> A) -> Prop, ((WF A lt2) /\ ((forall x : num -> A, (~ (bad x)) -> exists n : num, forall y : num -> A, (forall k : num, (lt k n) -> (y k) = (x k)) -> ~ (bad y)) /\ (exists x : num -> A, bad x))) -> exists y : num -> A, (bad y) /\ (forall z : num -> A, forall n : num, ((bad z) /\ (forall k : num, (lt k n) -> (z k) = (y k))) -> ~ (lt2 (z n) (y n))).
Axiom thm_WF_REC_TAIL : forall (A B : Type'), forall P : A -> Prop, forall g : A -> A, forall h : A -> B, exists f : A -> B, forall x : A, (f x) = (@COND B (P x) (f (g x)) (h x)).
Axiom thm_WF_REC_TAIL_GENERAL : forall (A B : Type') (lt2 : A -> A -> Prop), forall P : (A -> B) -> A -> Prop, forall G : (A -> B) -> A -> A, forall H : (A -> B) -> A -> B, ((WF A lt2) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> ((P f x) = (P g x)) /\ (((G f x) = (G g x)) /\ ((H f x) = (H g x)))) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) /\ (forall f : A -> B, forall x : A, forall y : A, ((P f x) /\ (lt2 y (G f x))) -> lt2 y x)))) -> exists f : A -> B, forall x : A, (f x) = (@COND B (P f x) (f (G f x)) (H f x)).
Axiom thm_ARITH_ZERO : ((NUMERAL (NUMERAL _0)) = (NUMERAL _0)) /\ ((BIT0 _0) = _0).
Axiom thm_BIT0_0 : (BIT0 (NUMERAL _0)) = (NUMERAL _0).
Axiom thm_BIT1_0 : (BIT1 (NUMERAL _0)) = (NUMERAL (BIT1 _0)).
Axiom thm_ARITH_SUC : (forall n : num, (SUC (NUMERAL n)) = (NUMERAL (SUC n))) /\ (((SUC _0) = (BIT1 _0)) /\ ((forall n : num, (SUC (BIT0 n)) = (BIT1 n)) /\ (forall n : num, (SUC (BIT1 n)) = (BIT0 (SUC n))))).
Axiom thm_ARITH_PRE : (forall n : num, (PRE (NUMERAL n)) = (NUMERAL (PRE n))) /\ (((PRE _0) = _0) /\ ((forall n : num, (PRE (BIT0 n)) = (@COND num (n = _0) _0 (BIT1 (PRE n)))) /\ (forall n : num, (PRE (BIT1 n)) = (BIT0 n)))).
Axiom thm_ARITH_ADD : (forall m : num, forall n : num, (add (NUMERAL m) (NUMERAL n)) = (NUMERAL (add m n))) /\ (((add _0 _0) = _0) /\ ((forall n : num, (add _0 (BIT0 n)) = (BIT0 n)) /\ ((forall n : num, (add _0 (BIT1 n)) = (BIT1 n)) /\ ((forall n : num, (add (BIT0 n) _0) = (BIT0 n)) /\ ((forall n : num, (add (BIT1 n) _0) = (BIT1 n)) /\ ((forall m : num, forall n : num, (add (BIT0 m) (BIT0 n)) = (BIT0 (add m n))) /\ ((forall m : num, forall n : num, (add (BIT0 m) (BIT1 n)) = (BIT1 (add m n))) /\ ((forall m : num, forall n : num, (add (BIT1 m) (BIT0 n)) = (BIT1 (add m n))) /\ (forall m : num, forall n : num, (add (BIT1 m) (BIT1 n)) = (BIT0 (SUC (add m n)))))))))))).
Axiom thm_ARITH_MULT : (forall m : num, forall n : num, (mul (NUMERAL m) (NUMERAL n)) = (NUMERAL (mul m n))) /\ (((mul _0 _0) = _0) /\ ((forall n : num, (mul _0 (BIT0 n)) = _0) /\ ((forall n : num, (mul _0 (BIT1 n)) = _0) /\ ((forall n : num, (mul (BIT0 n) _0) = _0) /\ ((forall n : num, (mul (BIT1 n) _0) = _0) /\ ((forall m : num, forall n : num, (mul (BIT0 m) (BIT0 n)) = (BIT0 (BIT0 (mul m n)))) /\ ((forall m : num, forall n : num, (mul (BIT0 m) (BIT1 n)) = (add (BIT0 m) (BIT0 (BIT0 (mul m n))))) /\ ((forall m : num, forall n : num, (mul (BIT1 m) (BIT0 n)) = (add (BIT0 n) (BIT0 (BIT0 (mul m n))))) /\ (forall m : num, forall n : num, (mul (BIT1 m) (BIT1 n)) = (add (BIT1 m) (add (BIT0 n) (BIT0 (BIT0 (mul m n)))))))))))))).
Axiom thm_ARITH_EXP : (forall m : num, forall n : num, (EXP (NUMERAL m) (NUMERAL n)) = (NUMERAL (EXP m n))) /\ (((EXP _0 _0) = (BIT1 _0)) /\ ((forall m : num, (EXP (BIT0 m) _0) = (BIT1 _0)) /\ ((forall m : num, (EXP (BIT1 m) _0) = (BIT1 _0)) /\ ((forall n : num, (EXP _0 (BIT0 n)) = (mul (EXP _0 n) (EXP _0 n))) /\ ((forall m : num, forall n : num, (EXP (BIT0 m) (BIT0 n)) = (mul (EXP (BIT0 m) n) (EXP (BIT0 m) n))) /\ ((forall m : num, forall n : num, (EXP (BIT1 m) (BIT0 n)) = (mul (EXP (BIT1 m) n) (EXP (BIT1 m) n))) /\ ((forall n : num, (EXP _0 (BIT1 n)) = _0) /\ ((forall m : num, forall n : num, (EXP (BIT0 m) (BIT1 n)) = (mul (BIT0 m) (mul (EXP (BIT0 m) n) (EXP (BIT0 m) n)))) /\ (forall m : num, forall n : num, (EXP (BIT1 m) (BIT1 n)) = (mul (BIT1 m) (mul (EXP (BIT1 m) n) (EXP (BIT1 m) n)))))))))))).
Axiom thm_ARITH_EVEN : (forall n : num, (EVEN (NUMERAL n)) = (EVEN n)) /\ (((EVEN _0) = True) /\ ((forall n : num, (EVEN (BIT0 n)) = True) /\ (forall n : num, (EVEN (BIT1 n)) = False))).
Axiom thm_ARITH_ODD : (forall n : num, (ODD (NUMERAL n)) = (ODD n)) /\ (((ODD _0) = False) /\ ((forall n : num, (ODD (BIT0 n)) = False) /\ (forall n : num, (ODD (BIT1 n)) = True))).
Axiom thm_ARITH_LE : (forall m : num, forall n : num, (le (NUMERAL m) (NUMERAL n)) = (le m n)) /\ (((le _0 _0) = True) /\ ((forall n : num, (le (BIT0 n) _0) = (le n _0)) /\ ((forall n : num, (le (BIT1 n) _0) = False) /\ ((forall n : num, (le _0 (BIT0 n)) = True) /\ ((forall n : num, (le _0 (BIT1 n)) = True) /\ ((forall m : num, forall n : num, (le (BIT0 m) (BIT0 n)) = (le m n)) /\ ((forall m : num, forall n : num, (le (BIT0 m) (BIT1 n)) = (le m n)) /\ ((forall m : num, forall n : num, (le (BIT1 m) (BIT0 n)) = (lt m n)) /\ (forall m : num, forall n : num, (le (BIT1 m) (BIT1 n)) = (le m n)))))))))).
Axiom thm_ARITH_LT : (forall m : num, forall n : num, (lt (NUMERAL m) (NUMERAL n)) = (lt m n)) /\ (((lt _0 _0) = False) /\ ((forall n : num, (lt (BIT0 n) _0) = False) /\ ((forall n : num, (lt (BIT1 n) _0) = False) /\ ((forall n : num, (lt _0 (BIT0 n)) = (lt _0 n)) /\ ((forall n : num, (lt _0 (BIT1 n)) = True) /\ ((forall m : num, forall n : num, (lt (BIT0 m) (BIT0 n)) = (lt m n)) /\ ((forall m : num, forall n : num, (lt (BIT0 m) (BIT1 n)) = (le m n)) /\ ((forall m : num, forall n : num, (lt (BIT1 m) (BIT0 n)) = (lt m n)) /\ (forall m : num, forall n : num, (lt (BIT1 m) (BIT1 n)) = (lt m n)))))))))).
Axiom thm_ARITH_EQ : (forall m : num, forall n : num, ((NUMERAL m) = (NUMERAL n)) = (m = n)) /\ (((_0 = _0) = True) /\ ((forall n : num, ((BIT0 n) = _0) = (n = _0)) /\ ((forall n : num, ((BIT1 n) = _0) = False) /\ ((forall n : num, (_0 = (BIT0 n)) = (_0 = n)) /\ ((forall n : num, (_0 = (BIT1 n)) = False) /\ ((forall m : num, forall n : num, ((BIT0 m) = (BIT0 n)) = (m = n)) /\ ((forall m : num, forall n : num, ((BIT0 m) = (BIT1 n)) = False) /\ ((forall m : num, forall n : num, ((BIT1 m) = (BIT0 n)) = False) /\ (forall m : num, forall n : num, ((BIT1 m) = (BIT1 n)) = (m = n)))))))))).
Axiom thm_ARITH_SUB : (forall m : num, forall n : num, (minus (NUMERAL m) (NUMERAL n)) = (NUMERAL (minus m n))) /\ (((minus _0 _0) = _0) /\ ((forall n : num, (minus _0 (BIT0 n)) = _0) /\ ((forall n : num, (minus _0 (BIT1 n)) = _0) /\ ((forall n : num, (minus (BIT0 n) _0) = (BIT0 n)) /\ ((forall n : num, (minus (BIT1 n) _0) = (BIT1 n)) /\ ((forall m : num, forall n : num, (minus (BIT0 m) (BIT0 n)) = (BIT0 (minus m n))) /\ ((forall m : num, forall n : num, (minus (BIT0 m) (BIT1 n)) = (PRE (BIT0 (minus m n)))) /\ ((forall m : num, forall n : num, (minus (BIT1 m) (BIT0 n)) = (@COND num (le n m) (BIT1 (minus m n)) _0)) /\ (forall m : num, forall n : num, (minus (BIT1 m) (BIT1 n)) = (BIT0 (minus m n))))))))))).
Axiom thm_EXP_2_NE_0 : forall n : num, ~ ((EXP (NUMERAL (BIT0 (BIT1 _0))) n) = (NUMERAL _0)).
Axiom thm_INJ_INVERSE2 : forall (A B C : Type'), forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Axiom thm_NUMPAIR : forall x : num, forall y : num, (NUMPAIR x y) = (mul (EXP (NUMERAL (BIT0 (BIT1 _0))) x) (add (mul (NUMERAL (BIT0 (BIT1 _0))) y) (NUMERAL (BIT1 _0)))).
Axiom thm_NUMPAIR_INJ_LEMMA : forall x1 : num, forall y1 : num, forall x2 : num, forall y2 : num, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) -> x1 = x2.
Axiom thm_NUMPAIR_INJ : forall x1 : num, forall y1 : num, forall x2 : num, forall y2 : num, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Axiom thm_NUMSUM : forall b : Prop, forall x : num, (NUMSUM b x) = (@COND num b (SUC (mul (NUMERAL (BIT0 (BIT1 _0))) x)) (mul (NUMERAL (BIT0 (BIT1 _0))) x)).
Axiom thm_NUMSUM_INJ : forall b1 : Prop, forall x1 : num, forall b2 : Prop, forall x2 : num, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Axiom thm_INJN : forall (A : Type'), forall m : num, (INJN A m) = (fun n : num => fun a : A => n = m).
Axiom thm_INJN_INJ : forall (A : Type'), forall n1 : num, forall n2 : num, ((INJN A n1) = (INJN A n2)) = (n1 = n2).
Axiom thm_INJA : forall (A : Type'), forall a : A, (INJA A a) = (fun n : num => fun b : A => b = a).
Axiom thm_INJA_INJ : forall (A : Type'), forall a1 : A, forall a2 : A, ((INJA A a1) = (INJA A a2)) = (a1 = a2).
Axiom thm_INJF : forall (A : Type'), forall f : num -> num -> A -> Prop, (INJF A f) = (fun n : num => f (NUMFST n) (NUMSND n)).
Axiom thm_INJF_INJ : forall (A : Type'), forall f1 : num -> num -> A -> Prop, forall f2 : num -> num -> A -> Prop, ((INJF A f1) = (INJF A f2)) = (f1 = f2).
Axiom thm_INJP : forall (A : Type'), forall f1 : num -> A -> Prop, forall f2 : num -> A -> Prop, (INJP A f1 f2) = (fun n : num => fun a : A => @COND Prop (NUMLEFT n) (f1 (NUMRIGHT n) a) (f2 (NUMRIGHT n) a)).
Axiom thm_INJP_INJ : forall (A : Type'), forall f1 : num -> A -> Prop, forall f1' : num -> A -> Prop, forall f2 : num -> A -> Prop, forall f2' : num -> A -> Prop, ((INJP A f1 f2) = (INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Axiom thm_ZCONSTR : forall (A : Type'), forall c : num, forall i : A, forall r : num -> num -> A -> Prop, (ZCONSTR A c i r) = (INJP A (INJN A (SUC c)) (INJP A (INJA A i) (INJF A r))).
Axiom thm_ZBOT : forall (A : Type'), (ZBOT A) = (INJP A (INJN A (NUMERAL _0)) (@ε (num -> A -> Prop) (fun z : num -> A -> Prop => True))).
Axiom thm_ZCONSTR_ZBOT : forall (A : Type'), forall c : num, forall i : A, forall r : num -> num -> A -> Prop, ~ ((ZCONSTR A c i r) = (ZBOT A)).
Axiom thm_ZRECSPACE_RULES : forall (A : Type'), (ZRECSPACE A (ZBOT A)) /\ (forall c : num, forall i : A, forall r : num -> num -> A -> Prop, (forall n : num, ZRECSPACE A (r n)) -> ZRECSPACE A (ZCONSTR A c i r)).
Axiom thm_ZRECSPACE_CASES : forall (A : Type'), forall a : num -> A -> Prop, (ZRECSPACE A a) = ((a = (ZBOT A)) \/ (exists c : num, exists i : A, exists r : num -> num -> A -> Prop, (a = (ZCONSTR A c i r)) /\ (forall n : num, ZRECSPACE A (r n)))).
Axiom thm_ZRECSPACE_INDUCT : forall (A : Type'), forall ZRECSPACE' : (num -> A -> Prop) -> Prop, ((ZRECSPACE' (ZBOT A)) /\ (forall c : num, forall i : A, forall r : num -> num -> A -> Prop, (forall n : num, ZRECSPACE' (r n)) -> ZRECSPACE' (ZCONSTR A c i r))) -> forall a : num -> A -> Prop, (ZRECSPACE A a) -> ZRECSPACE' a.
Axiom thm_BOTTOM : forall (A : Type'), (BOTTOM A) = (_mk_rec A (ZBOT A)).
Axiom thm_CONSTR : forall (A : Type'), forall c : num, forall i : A, forall r : num -> recspace A, (CONSTR A c i r) = (_mk_rec A (ZCONSTR A c i (fun n : num => _dest_rec A (r n)))).
Axiom thm_MK_REC_INJ : forall (A : Type'), forall x : num -> A -> Prop, forall y : num -> A -> Prop, ((_mk_rec A x) = (_mk_rec A y)) -> ((ZRECSPACE A x) /\ (ZRECSPACE A y)) -> x = y.
Axiom thm_DEST_REC_INJ : forall (A : Type'), forall x : recspace A, forall y : recspace A, ((_dest_rec A x) = (_dest_rec A y)) = (x = y).
Axiom thm_CONSTR_BOT : forall (A : Type'), forall c : num, forall i : A, forall r : num -> recspace A, ~ ((CONSTR A c i r) = (BOTTOM A)).
Axiom thm_CONSTR_INJ : forall (A : Type'), forall c1 : num, forall i1 : A, forall r1 : num -> recspace A, forall c2 : num, forall i2 : A, forall r2 : num -> recspace A, ((CONSTR A c1 i1 r1) = (CONSTR A c2 i2 r2)) = ((c1 = c2) /\ ((i1 = i2) /\ (r1 = r2))).
Axiom thm_CONSTR_IND : forall (A : Type'), forall P : (recspace A) -> Prop, ((P (BOTTOM A)) /\ (forall c : num, forall i : A, forall r : num -> recspace A, (forall n : num, P (r n)) -> P (CONSTR A c i r))) -> forall x : recspace A, P x.
Axiom thm_CONSTR_REC : forall (A B : Type'), forall Fn : num -> A -> (num -> recspace A) -> (num -> B) -> B, exists f : (recspace A) -> B, forall c : num, forall i : A, forall r : num -> recspace A, (f (CONSTR A c i r)) = (Fn c i r (fun n : num => f (r n))).
Axiom thm_FCONS : forall (A : Type'), (forall a : A, forall f : num -> A, (FCONS A a f (NUMERAL _0)) = a) /\ (forall a : A, forall f : num -> A, forall n : num, (FCONS A a f (SUC n)) = (f n)).
Axiom thm_FCONS_UNDO : forall (A : Type'), forall f : num -> A, f = (FCONS A (f (NUMERAL _0)) (o num num A f SUC)).
Axiom thm_FNIL : forall (A : Type'), forall n : num, (FNIL A n) = (@ε A (fun x : A => True)).
Axiom thm_sum_INDUCT : forall (A B : Type'), forall P : (Sum A B) -> Prop, ((forall a : A, P (INL A B a)) /\ (forall a : B, P (INR A B a))) -> forall x : Sum A B, P x.
Axiom thm_sum_RECURSION : forall (A B Z' : Type'), forall INL' : A -> Z', forall INR' : B -> Z', exists fn : (Sum A B) -> Z', (forall a : A, (fn (INL A B a)) = (INL' a)) /\ (forall a : B, (fn (INR A B a)) = (INR' a)).
Axiom thm_OUTL : forall (A B : Type') (x : A), (OUTL A B (INL A B x)) = x.
Axiom thm_OUTR : forall (A B : Type') (y : B), (OUTR A B (INR A B y)) = y.
Axiom thm_option_INDUCT : forall (A : Type'), forall P : (option A) -> Prop, ((P (NONE A)) /\ (forall a : A, P (SOME A a))) -> forall x : option A, P x.
Axiom thm_option_RECURSION : forall (A Z' : Type'), forall NONE' : Z', forall SOME' : A -> Z', exists fn : (option A) -> Z', ((fn (NONE A)) = NONE') /\ (forall a : A, (fn (SOME A a)) = (SOME' a)).
Axiom thm_list_INDUCT : forall (A : Type'), forall P : (list A) -> Prop, ((P (NIL A)) /\ (forall a0 : A, forall a1 : list A, (P a1) -> P (CONS A a0 a1))) -> forall x : list A, P x.
Axiom thm_list_RECURSION : forall (A Z' : Type'), forall NIL' : Z', forall CONS' : A -> (list A) -> Z' -> Z', exists fn : (list A) -> Z', ((fn (NIL A)) = NIL') /\ (forall a0 : A, forall a1 : list A, (fn (CONS A a0 a1)) = (CONS' a0 a1 (fn a1))).
Axiom thm_FORALL_OPTION_THM : forall (A : Type'), forall P : (option A) -> Prop, (forall x : option A, P x) = ((P (NONE A)) /\ (forall a : A, P (SOME A a))).
Axiom thm_EXISTS_OPTION_THM : forall (A : Type'), forall P : (option A) -> Prop, (exists x : option A, P x) = ((P (NONE A)) \/ (exists a : A, P (SOME A a))).
Axiom thm_option_DISTINCT : forall (A : Type'), forall a : A, ~ ((SOME A a) = (NONE A)).
Axiom thm_option_INJ : forall (A : Type'), forall a : A, forall b : A, ((SOME A a) = (SOME A b)) = (a = b).
Axiom thm_ISO : forall (A B : Type'), forall g : B -> A, forall f : A -> B, (ISO A B f g) = ((forall x : B, (f (g x)) = x) /\ (forall y : A, (g (f y)) = y)).
Axiom thm_ISO_REFL : forall (A : Type'), ISO A A (fun x : A => x) (fun x : A => x).
Axiom thm_ISO_FUN : forall (A A' B B' : Type') (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A'), ((ISO A A' f f') /\ (ISO B B' g g')) -> ISO (A -> B) (A' -> B') (fun h : A -> B => fun a' : A' => g (h (f' a'))) (fun h : A' -> B' => fun a : A => g' (h (f a))).
Axiom thm_ISO_USAGE : forall (A B : Type') (g : B -> A) (f : A -> B), (ISO A B f g) -> (forall P : A -> Prop, (forall x : A, P x) = (forall x : B, P (g x))) /\ ((forall P : A -> Prop, (exists x : A, P x) = (exists x : B, P (g x))) /\ (forall a : A, forall b : B, (a = (g b)) = ((f a) = b))).
Axiom thm_HD : forall (A : Type') (t : list A) (h : A), (HD A (CONS A h t)) = h.
Axiom thm_TL : forall (A : Type') (h : A) (t : list A), (TL A (CONS A h t)) = t.
Axiom thm_APPEND : forall (A : Type'), (forall l : list A, (APPEND A (NIL A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND A (CONS A h t) l) = (CONS A h (APPEND A t l))).
Axiom thm_REVERSE : forall (A : Type') (l : list A) (x : A), ((REVERSE A (NIL A)) = (NIL A)) /\ ((REVERSE A (CONS A x l)) = (APPEND A (REVERSE A l) (CONS A x (NIL A)))).
Axiom thm_LENGTH : forall (A : Type'), ((LENGTH A (NIL A)) = (NUMERAL _0)) /\ (forall h : A, forall t : list A, (LENGTH A (CONS A h t)) = (SUC (LENGTH A t))).
Axiom thm_MAP : forall (A B : Type'), (forall f : A -> B, (MAP A B f (NIL A)) = (NIL B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP A B f (CONS A h t)) = (CONS B (f h) (MAP A B f t))).
Axiom thm_LAST : forall (A : Type') (h : A) (t : list A), (LAST A (CONS A h t)) = (@COND A (t = (NIL A)) h (LAST A t)).
Axiom thm_BUTLAST : forall (A : Type') (h : A) (t : list A), ((BUTLAST A (NIL A)) = (NIL A)) /\ ((BUTLAST A (CONS A h t)) = (@COND (list A) (t = (NIL A)) (NIL A) (CONS A h (BUTLAST A t)))).
Axiom thm_REPLICATE : forall (A : Type') (n : num) (x : A), ((REPLICATE A (NUMERAL _0) x) = (NIL A)) /\ ((REPLICATE A (SUC n) x) = (CONS A x (REPLICATE A n x))).
Axiom thm_NULL : forall (A : Type') (h : A) (t : list A), ((NULL A (NIL A)) = True) /\ ((NULL A (CONS A h t)) = False).
Axiom thm_ALL : forall (A : Type') (h : A) (P : A -> Prop) (t : list A), ((ALL A P (NIL A)) = True) /\ ((ALL A P (CONS A h t)) = ((P h) /\ (ALL A P t))).
Axiom thm_EX : forall (A : Type') (h : A) (P : A -> Prop) (t : list A), ((EX A P (NIL A)) = False) /\ ((EX A P (CONS A h t)) = ((P h) \/ (EX A P t))).
Axiom thm_ITLIST : forall (A B : Type') (h : A) (f : A -> B -> B) (t : list A) (b : B), ((ITLIST A B f (NIL A) b) = b) /\ ((ITLIST A B f (CONS A h t) b) = (f h (ITLIST A B f t b))).
Axiom thm_MEM : forall (A : Type') (h : A) (x : A) (t : list A), ((MEM A x (NIL A)) = False) /\ ((MEM A x (CONS A h t)) = ((x = h) \/ (MEM A x t))).
Axiom thm_ALL2_DEF : forall (A B : Type') (h1' : A) (P : A -> B -> Prop) (t1 : list A) (l2 : list B), ((ALL2 A B P (NIL A) l2) = (l2 = (NIL B))) /\ ((ALL2 A B P (CONS A h1' t1) l2) = (@COND Prop (l2 = (NIL B)) False ((P h1' (HD B l2)) /\ (ALL2 A B P t1 (TL B l2))))).
Axiom thm_ALL2 : forall (A B : Type') (h1' : A) (h2' : B) (P : A -> B -> Prop) (t1 : list A) (t2 : list B), ((ALL2 A B P (NIL A) (NIL B)) = True) /\ (((ALL2 A B P (CONS A h1' t1) (NIL B)) = False) /\ (((ALL2 A B P (NIL A) (CONS B h2' t2)) = False) /\ ((ALL2 A B P (CONS A h1' t1) (CONS B h2' t2)) = ((P h1' h2') /\ (ALL2 A B P t1 t2))))).
Axiom thm_MAP2_DEF : forall (A B C : Type') (h1' : A) (f : A -> B -> C) (t1 : list A) (l : list B), ((MAP2 A B C f (NIL A) l) = (NIL C)) /\ ((MAP2 A B C f (CONS A h1' t1) l) = (CONS C (f h1' (HD B l)) (MAP2 A B C f t1 (TL B l)))).
Axiom thm_MAP2 : forall (A B C : Type') (h1' : A) (h2' : B) (f : A -> B -> C) (t1 : list A) (t2 : list B), ((MAP2 A B C f (NIL A) (NIL B)) = (NIL C)) /\ ((MAP2 A B C f (CONS A h1' t1) (CONS B h2' t2)) = (CONS C (f h1' h2') (MAP2 A B C f t1 t2))).
Axiom thm_EL : forall (A : Type') (n : num) (l : list A), ((EL A (NUMERAL _0) l) = (HD A l)) /\ ((EL A (SUC n) l) = (EL A n (TL A l))).
Axiom thm_FILTER : forall (A : Type') (h : A) (P : A -> Prop) (t : list A), ((FILTER A P (NIL A)) = (NIL A)) /\ ((FILTER A P (CONS A h t)) = (@COND (list A) (P h) (CONS A h (FILTER A P t)) (FILTER A P t))).
Axiom thm_ASSOC : forall (A B : Type') (h : prod A B) (a : A) (t : list (prod A B)), (ASSOC A B a (CONS (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (ASSOC A B a t)).
Axiom thm_ITLIST2_DEF : forall (A B C : Type') (h1' : A) (f : A -> B -> C -> C) (t1 : list A) (l2 : list B) (b : C), ((ITLIST2 A B C f (NIL A) l2 b) = b) /\ ((ITLIST2 A B C f (CONS A h1' t1) l2 b) = (f h1' (HD B l2) (ITLIST2 A B C f t1 (TL B l2) b))).
Axiom thm_ITLIST2 : forall (A B C : Type') (h1' : A) (h2' : B) (f : A -> B -> C -> C) (t1 : list A) (t2 : list B) (b : C), ((ITLIST2 A B C f (NIL A) (NIL B) b) = b) /\ ((ITLIST2 A B C f (CONS A h1' t1) (CONS B h2' t2) b) = (f h1' h2' (ITLIST2 A B C f t1 t2 b))).
Axiom thm_ZIP_DEF : forall (A B : Type') (h1' : A) (t1 : list A) (l2 : list B), ((ZIP A B (NIL A) l2) = (NIL (prod A B))) /\ ((ZIP A B (CONS A h1' t1) l2) = (CONS (prod A B) (@pair A B h1' (HD B l2)) (ZIP A B t1 (TL B l2)))).
Axiom thm_ZIP : forall (A B : Type') (h1' : A) (h2' : B) (t1 : list A) (t2 : list B), ((ZIP A B (NIL A) (NIL B)) = (NIL (prod A B))) /\ ((ZIP A B (CONS A h1' t1) (CONS B h2' t2)) = (CONS (prod A B) (@pair A B h1' h2') (ZIP A B t1 t2))).
Axiom thm_ALLPAIRS : forall (A B : Type') (h : A) (f : A -> B -> Prop) (t : list A) (l : list B), ((ALLPAIRS A B f (NIL A) l) = True) /\ ((ALLPAIRS A B f (CONS A h t) l) = ((ALL B (f h) l) /\ (ALLPAIRS A B f t l))).
Axiom thm_PAIRWISE : forall (A : Type') (h : A) (r : A -> A -> Prop) (t : list A), ((PAIRWISE A r (NIL A)) = True) /\ ((PAIRWISE A r (CONS A h t)) = ((ALL A (r h) t) /\ (PAIRWISE A r t))).
Axiom thm_list_of_seq : forall (A : Type') (s : num -> A) (n : num), ((list_of_seq A s (NUMERAL _0)) = (NIL A)) /\ ((list_of_seq A s (SUC n)) = (APPEND A (list_of_seq A s n) (CONS A (s n) (NIL A)))).
Axiom thm_NOT_CONS_NIL : forall (A : Type'), forall h : A, forall t : list A, ~ ((CONS A h t) = (NIL A)).
Axiom thm_LAST_CLAUSES : forall (A : Type') (h : A) (k : A) (t : list A), ((LAST A (CONS A h (NIL A))) = h) /\ ((LAST A (CONS A h (CONS A k t))) = (LAST A (CONS A k t))).
Axiom thm_APPEND_NIL : forall (A : Type'), forall l : list A, (APPEND A l (NIL A)) = l.
Axiom thm_APPEND_ASSOC : forall (A : Type'), forall l : list A, forall m : list A, forall n : list A, (APPEND A l (APPEND A m n)) = (APPEND A (APPEND A l m) n).
Axiom thm_REVERSE_APPEND : forall (A : Type'), forall l : list A, forall m : list A, (REVERSE A (APPEND A l m)) = (APPEND A (REVERSE A m) (REVERSE A l)).
Axiom thm_REVERSE_REVERSE : forall (A : Type'), forall l : list A, (REVERSE A (REVERSE A l)) = l.
Axiom thm_REVERSE_EQ_EMPTY : forall (A : Type'), forall l : list A, ((REVERSE A l) = (NIL A)) = (l = (NIL A)).
Axiom thm_CONS_11 : forall (A : Type'), forall h1' : A, forall h2' : A, forall t1 : list A, forall t2 : list A, ((CONS A h1' t1) = (CONS A h2' t2)) = ((h1' = h2') /\ (t1 = t2)).
Axiom thm_list_CASES : forall (A : Type'), forall l : list A, (l = (NIL A)) \/ (exists h : A, exists t : list A, l = (CONS A h t)).
Axiom thm_LIST_EQ : forall (A : Type'), forall l1 : list A, forall l2 : list A, (l1 = l2) = (((LENGTH A l1) = (LENGTH A l2)) /\ (forall n : num, (lt n (LENGTH A l2)) -> (EL A n l1) = (EL A n l2))).
Axiom thm_LENGTH_APPEND : forall (A : Type'), forall l : list A, forall m : list A, (LENGTH A (APPEND A l m)) = (add (LENGTH A l) (LENGTH A m)).
Axiom thm_MAP_APPEND : forall (A B : Type'), forall f : A -> B, forall l1 : list A, forall l2 : list A, (MAP A B f (APPEND A l1 l2)) = (APPEND B (MAP A B f l1) (MAP A B f l2)).
Axiom thm_LENGTH_MAP : forall (A B : Type'), forall l : list A, forall f : A -> B, (LENGTH B (MAP A B f l)) = (LENGTH A l).
Axiom thm_LENGTH_EQ_NIL : forall (A : Type'), forall l : list A, ((LENGTH A l) = (NUMERAL _0)) = (l = (NIL A)).
Axiom thm_LENGTH_EQ_CONS : forall (A : Type'), forall l : list A, forall n : num, ((LENGTH A l) = (SUC n)) = (exists h : A, exists t : list A, (l = (CONS A h t)) /\ ((LENGTH A t) = n)).
Axiom thm_LENGTH_REVERSE : forall (A : Type'), forall l : list A, (LENGTH A (REVERSE A l)) = (LENGTH A l).
Axiom thm_MAP_o : forall (A B C : Type'), forall f : A -> B, forall g : B -> C, forall l : list A, (MAP A C (o A B C g f) l) = (MAP B C g (MAP A B f l)).
Axiom thm_MAP_EQ : forall (A B : Type'), forall f : A -> B, forall g : A -> B, forall l : list A, (ALL A (fun x : A => (f x) = (g x)) l) -> (MAP A B f l) = (MAP A B g l).
Axiom thm_ALL_IMP : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((forall x : A, ((MEM A x l) /\ (P x)) -> Q x) /\ (ALL A P l)) -> ALL A Q l.
Axiom thm_NOT_EX : forall (A : Type'), forall P : A -> Prop, forall l : list A, (~ (EX A P l)) = (ALL A (fun x : A => ~ (P x)) l).
Axiom thm_NOT_ALL : forall (A : Type'), forall P : A -> Prop, forall l : list A, (~ (ALL A P l)) = (EX A (fun x : A => ~ (P x)) l).
Axiom thm_ALL_MAP : forall (A B : Type'), forall P : B -> Prop, forall f : A -> B, forall l : list A, (ALL B P (MAP A B f l)) = (ALL A (o A B Prop P f) l).
Axiom thm_ALL_EQ : forall (A : Type') (R' : A -> Prop) (P : A -> Prop) (Q : A -> Prop), forall l : list A, ((ALL A R' l) /\ (forall x : A, (R' x) -> (P x) = (Q x))) -> (ALL A P l) = (ALL A Q l).
Axiom thm_ALL_T : forall (A : Type'), forall l : list A, ALL A (fun x : A => True) l.
Axiom thm_MAP_EQ_ALL2 : forall (A B : Type'), forall f : A -> B, forall l : list A, forall m : list A, (ALL2 A A (fun x : A => fun y : A => (f x) = (f y)) l m) -> (MAP A B f l) = (MAP A B f m).
Axiom thm_ALL2_MAP : forall (A B : Type'), forall P : B -> A -> Prop, forall f : A -> B, forall l : list A, (ALL2 B A P (MAP A B f l) l) = (ALL A (fun a : A => P (f a) a) l).
Axiom thm_MAP_EQ_DEGEN : forall (A : Type'), forall l : list A, forall f : A -> A, (ALL A (fun x : A => (f x) = x) l) -> (MAP A A f l) = l.
Axiom thm_ALL2_AND_RIGHT : forall (A B : Type'), forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : A -> B -> Prop, (ALL2 A B (fun x : A => fun y : B => (P x) /\ (Q x y)) l m) = ((ALL A P l) /\ (ALL2 A B Q l m)).
Axiom thm_ITLIST_APPEND : forall (A B : Type'), forall f : A -> B -> B, forall a : B, forall l1 : list A, forall l2 : list A, (ITLIST A B f (APPEND A l1 l2) a) = (ITLIST A B f l1 (ITLIST A B f l2 a)).
Axiom thm_ITLIST_EXTRA : forall (A B : Type') (a : A) (b : B), forall f : A -> B -> B, forall l : list A, (ITLIST A B f (APPEND A l (CONS A a (NIL A))) b) = (ITLIST A B f l (f a b)).
Axiom thm_ALL_MP : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((ALL A (fun x : A => (P x) -> Q x) l) /\ (ALL A P l)) -> ALL A Q l.
Axiom thm_AND_ALL : forall (A : Type') (P : A -> Prop) (Q : A -> Prop), forall l : list A, ((ALL A P l) /\ (ALL A Q l)) = (ALL A (fun x : A => (P x) /\ (Q x)) l).
Axiom thm_EX_IMP : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((forall x : A, ((MEM A x l) /\ (P x)) -> Q x) /\ (EX A P l)) -> EX A Q l.
Axiom thm_ALL_MEM : forall (A : Type'), forall P : A -> Prop, forall l : list A, (forall x : A, (MEM A x l) -> P x) = (ALL A P l).
Axiom thm_LENGTH_REPLICATE : forall (A : Type'), forall n : num, forall x : A, (LENGTH A (REPLICATE A n x)) = n.
Axiom thm_MEM_REPLICATE : forall (A : Type'), forall n : num, forall x : A, forall y : A, (MEM A x (REPLICATE A n y)) = ((x = y) /\ (~ (n = (NUMERAL _0)))).
Axiom thm_EX_MAP : forall (A B : Type'), forall P : B -> Prop, forall f : A -> B, forall l : list A, (EX B P (MAP A B f l)) = (EX A (o A B Prop P f) l).
Axiom thm_EXISTS_EX : forall (A B : Type'), forall P : A -> B -> Prop, forall l : list B, (exists x : A, EX B (P x) l) = (EX B (fun s : B => exists x : A, P x s) l).
Axiom thm_FORALL_ALL : forall (A B : Type'), forall P : A -> B -> Prop, forall l : list B, (forall x : A, ALL B (P x) l) = (ALL B (fun s : B => forall x : A, P x s) l).
Axiom thm_MEM_APPEND : forall (A : Type'), forall x : A, forall l1 : list A, forall l2 : list A, (MEM A x (APPEND A l1 l2)) = ((MEM A x l1) \/ (MEM A x l2)).
Axiom thm_MEM_MAP : forall (A B : Type'), forall f : A -> B, forall y : B, forall l : list A, (MEM B y (MAP A B f l)) = (exists x : A, (MEM A x l) /\ (y = (f x))).
Axiom thm_FILTER_APPEND : forall (A : Type'), forall P : A -> Prop, forall l1 : list A, forall l2 : list A, (FILTER A P (APPEND A l1 l2)) = (APPEND A (FILTER A P l1) (FILTER A P l2)).
Axiom thm_FILTER_MAP : forall (A B : Type'), forall P : B -> Prop, forall f : A -> B, forall l : list A, (FILTER B P (MAP A B f l)) = (MAP A B f (FILTER A (o A B Prop P f) l)).
Axiom thm_MEM_FILTER : forall (A : Type'), forall P : A -> Prop, forall l : list A, forall x : A, (MEM A x (FILTER A P l)) = ((P x) /\ (MEM A x l)).
Axiom thm_EX_MEM : forall (A : Type'), forall P : A -> Prop, forall l : list A, (exists x : A, (P x) /\ (MEM A x l)) = (EX A P l).
Axiom thm_MAP_FST_ZIP : forall (A B : Type'), forall l1 : list A, forall l2 : list B, ((LENGTH A l1) = (LENGTH B l2)) -> (MAP (prod A B) A (@fst A B) (ZIP A B l1 l2)) = l1.
Axiom thm_MAP_SND_ZIP : forall (A B : Type'), forall l1 : list A, forall l2 : list B, ((LENGTH A l1) = (LENGTH B l2)) -> (MAP (prod A B) B (@snd A B) (ZIP A B l1 l2)) = l2.
Axiom thm_LENGTH_ZIP : forall (A B : Type'), forall l1 : list A, forall l2 : list B, ((LENGTH A l1) = (LENGTH B l2)) -> (LENGTH (prod A B) (ZIP A B l1 l2)) = (LENGTH B l2).
Axiom thm_MEM_ASSOC : forall (A B : Type'), forall l : list (prod A B), forall x : A, (MEM (prod A B) (@pair A B x (ASSOC A B x l)) l) = (MEM A x (MAP (prod A B) A (@fst A B) l)).
Axiom thm_ALL_APPEND : forall (A : Type'), forall P : A -> Prop, forall l1 : list A, forall l2 : list A, (ALL A P (APPEND A l1 l2)) = ((ALL A P l1) /\ (ALL A P l2)).
Axiom thm_MEM_EL : forall (A : Type'), forall l : list A, forall n : num, (lt n (LENGTH A l)) -> MEM A (EL A n l) l.
Axiom thm_MEM_EXISTS_EL : forall (A : Type'), forall l : list A, forall x : A, (MEM A x l) = (exists i : num, (lt i (LENGTH A l)) /\ (x = (EL A i l))).
Axiom thm_ALL_EL : forall (A : Type'), forall P : A -> Prop, forall l : list A, (forall i : num, (lt i (LENGTH A l)) -> P (EL A i l)) = (ALL A P l).
Axiom thm_ALL2_MAP2 : forall (A B C D : Type') (P : B -> D -> Prop), forall f : A -> B, forall g : C -> D, forall l : list A, forall m : list C, (ALL2 B D P (MAP A B f l) (MAP C D g m)) = (ALL2 A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_AND_ALL2 : forall (A B : Type'), forall P : A -> B -> Prop, forall Q : A -> B -> Prop, forall l : list A, forall m : list B, ((ALL2 A B P l m) /\ (ALL2 A B Q l m)) = (ALL2 A B (fun x : A => fun y : B => (P x y) /\ (Q x y)) l m).
Axiom thm_ALLPAIRS_SYM : forall (A B : Type'), forall P : A -> B -> Prop, forall l : list A, forall m : list B, (ALLPAIRS A B P l m) = (ALLPAIRS B A (fun x : B => fun y : A => P y x) m l).
Axiom thm_ALLPAIRS_MEM : forall (A B : Type'), forall P : A -> B -> Prop, forall l : list A, forall m : list B, (forall x : A, forall y : B, ((MEM A x l) /\ (MEM B y m)) -> P x y) = (ALLPAIRS A B P l m).
Axiom thm_ALLPAIRS_MAP : forall (A B C D : Type'), forall P : B -> D -> Prop, forall f : A -> B, forall g : C -> D, forall l : list A, forall m : list C, (ALLPAIRS B D P (MAP A B f l) (MAP C D g m)) = (ALLPAIRS A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_ALLPAIRS_EQ : forall (A B : Type') (R' : A -> B -> Prop) (R'' : A -> B -> Prop), forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : B -> Prop, ((ALL A P l) /\ ((ALL B Q m) /\ (forall p : A, forall q : B, ((P p) /\ (Q q)) -> (R' p q) = (R'' p q)))) -> (ALLPAIRS A B R' l m) = (ALLPAIRS A B R'' l m).
Axiom thm_ALL2_ALL : forall (A : Type'), forall P : A -> A -> Prop, forall l : list A, (ALL2 A A P l l) = (ALL A (fun x : A => P x x) l).
Axiom thm_APPEND_EQ_NIL : forall (A : Type'), forall l : list A, forall m : list A, ((APPEND A l m) = (NIL A)) = ((l = (NIL A)) /\ (m = (NIL A))).
Axiom thm_APPEND_LCANCEL : forall (A : Type'), forall l1 : list A, forall l2 : list A, forall l3 : list A, ((APPEND A l1 l2) = (APPEND A l1 l3)) = (l2 = l3).
Axiom thm_APPEND_RCANCEL : forall (A : Type'), forall l1 : list A, forall l2 : list A, forall l3 : list A, ((APPEND A l1 l3) = (APPEND A l2 l3)) = (l1 = l2).
Axiom thm_LENGTH_MAP2 : forall (A B C : Type'), forall f : A -> B -> C, forall l : list A, forall m : list B, ((LENGTH A l) = (LENGTH B m)) -> (LENGTH C (MAP2 A B C f l m)) = (LENGTH B m).
Axiom thm_EL_MAP2 : forall (A B C : Type'), forall f : A -> B -> C, forall l : list A, forall m : list B, forall k : num, ((lt k (LENGTH A l)) /\ (lt k (LENGTH B m))) -> (EL C k (MAP2 A B C f l m)) = (f (EL A k l) (EL B k m)).
Axiom thm_MAP_EQ_NIL : forall (A B : Type'), forall f : A -> B, forall l : list A, ((MAP A B f l) = (NIL B)) = (l = (NIL A)).
Axiom thm_INJECTIVE_MAP : forall (A B : Type'), forall f : A -> B, (forall l : list A, forall m : list A, ((MAP A B f l) = (MAP A B f m)) -> l = m) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_SURJECTIVE_MAP : forall (A B : Type'), forall f : A -> B, (forall m : list B, exists l : list A, (MAP A B f l) = m) = (forall y : B, exists x : A, (f x) = y).
Axiom thm_MAP_ID : forall (A : Type'), forall l : list A, (MAP A A (fun x : A => x) l) = l.
Axiom thm_MAP_I : forall (A : Type'), (MAP A A (I A)) = (I (list A)).
Axiom thm_BUTLAST_CLAUSES : forall (A : Type'), ((BUTLAST A (NIL A)) = (NIL A)) /\ ((forall a : A, (BUTLAST A (CONS A a (NIL A))) = (NIL A)) /\ (forall a : A, forall h : A, forall t : list A, (BUTLAST A (CONS A a (CONS A h t))) = (CONS A a (BUTLAST A (CONS A h t))))).
Axiom thm_BUTLAST_APPEND : forall (A : Type'), forall l : list A, forall m : list A, (BUTLAST A (APPEND A l m)) = (@COND (list A) (m = (NIL A)) (BUTLAST A l) (APPEND A l (BUTLAST A m))).
Axiom thm_APPEND_BUTLAST_LAST : forall (A : Type'), forall l : list A, (~ (l = (NIL A))) -> (APPEND A (BUTLAST A l) (CONS A (LAST A l) (NIL A))) = l.
Axiom thm_LAST_APPEND : forall (A : Type'), forall p : list A, forall q : list A, (LAST A (APPEND A p q)) = (@COND A (q = (NIL A)) (LAST A p) (LAST A q)).
Axiom thm_LENGTH_TL : forall (A : Type'), forall l : list A, (~ (l = (NIL A))) -> (LENGTH A (TL A l)) = (minus (LENGTH A l) (NUMERAL (BIT1 _0))).
Axiom thm_LAST_REVERSE : forall (A : Type'), forall l : list A, (~ (l = (NIL A))) -> (LAST A (REVERSE A l)) = (HD A l).
Axiom thm_HD_REVERSE : forall (A : Type'), forall l : list A, (~ (l = (NIL A))) -> (HD A (REVERSE A l)) = (LAST A l).
Axiom thm_EL_APPEND : forall (A : Type'), forall k : num, forall l : list A, forall m : list A, (EL A k (APPEND A l m)) = (@COND A (lt k (LENGTH A l)) (EL A k l) (EL A (minus k (LENGTH A l)) m)).
Axiom thm_EL_TL : forall (A : Type') (l : list A), forall n : num, (EL A n (TL A l)) = (EL A (add n (NUMERAL (BIT1 _0))) l).
Axiom thm_EL_CONS : forall (A : Type'), forall n : num, forall h : A, forall t : list A, (EL A n (CONS A h t)) = (@COND A (n = (NUMERAL _0)) h (EL A (minus n (NUMERAL (BIT1 _0))) t)).
Axiom thm_LAST_EL : forall (A : Type'), forall l : list A, (~ (l = (NIL A))) -> (LAST A l) = (EL A (minus (LENGTH A l) (NUMERAL (BIT1 _0))) l).
Axiom thm_HD_APPEND : forall (A : Type'), forall l : list A, forall m : list A, (HD A (APPEND A l m)) = (@COND A (l = (NIL A)) (HD A m) (HD A l)).
Axiom thm_CONS_HD_TL : forall (A : Type'), forall l : list A, (~ (l = (NIL A))) -> l = (CONS A (HD A l) (TL A l)).
Axiom thm_EL_MAP : forall (A B : Type'), forall f : A -> B, forall n : num, forall l : list A, (lt n (LENGTH A l)) -> (EL B n (MAP A B f l)) = (f (EL A n l)).
Axiom thm_MAP_REVERSE : forall (A B : Type'), forall f : A -> B, forall l : list A, (REVERSE B (MAP A B f l)) = (MAP A B f (REVERSE A l)).
Axiom thm_ALL_FILTER : forall (A : Type'), forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, (ALL A P (FILTER A Q l)) = (ALL A (fun x : A => (Q x) -> P x) l).
Axiom thm_APPEND_SING : forall (A : Type'), forall h : A, forall t : list A, (APPEND A (CONS A h (NIL A)) t) = (CONS A h t).
Axiom thm_MEM_APPEND_DECOMPOSE_LEFT : forall (A : Type'), forall x : A, forall l : list A, (MEM A x l) = (exists l1 : list A, exists l2 : list A, (~ (MEM A x l1)) /\ (l = (APPEND A l1 (CONS A x l2)))).
Axiom thm_MEM_APPEND_DECOMPOSE : forall (A : Type'), forall x : A, forall l : list A, (MEM A x l) = (exists l1 : list A, exists l2 : list A, l = (APPEND A l1 (CONS A x l2))).
Axiom thm_PAIRWISE_APPEND : forall (A : Type'), forall R' : A -> A -> Prop, forall l : list A, forall m : list A, (PAIRWISE A R' (APPEND A l m)) = ((PAIRWISE A R' l) /\ ((PAIRWISE A R' m) /\ (forall x : A, forall y : A, ((MEM A x l) /\ (MEM A y m)) -> R' x y))).
Axiom thm_PAIRWISE_MAP : forall (A B : Type'), forall R' : B -> B -> Prop, forall f : A -> B, forall l : list A, (PAIRWISE B R' (MAP A B f l)) = (PAIRWISE A (fun x : A => fun y : A => R' (f x) (f y)) l).
Axiom thm_PAIRWISE_IMPLIES : forall (A : Type'), forall R' : A -> A -> Prop, forall R'' : A -> A -> Prop, forall l : list A, ((PAIRWISE A R' l) /\ (forall x : A, forall y : A, ((MEM A x l) /\ ((MEM A y l) /\ (R' x y))) -> R'' x y)) -> PAIRWISE A R'' l.
Axiom thm_PAIRWISE_TRANSITIVE : forall (A : Type'), forall R' : A -> A -> Prop, forall x : A, forall y : A, forall l : list A, (forall x' : A, forall y' : A, forall z : A, ((R' x' y') /\ (R' y' z)) -> R' x' z) -> (PAIRWISE A R' (CONS A x (CONS A y l))) = ((R' x y) /\ (PAIRWISE A R' (CONS A y l))).
Axiom thm_LENGTH_LIST_OF_SEQ : forall (A : Type'), forall s : num -> A, forall n : num, (LENGTH A (list_of_seq A s n)) = n.
Axiom thm_EL_LIST_OF_SEQ : forall (A : Type'), forall s : num -> A, forall m : num, forall n : num, (lt m n) -> (EL A m (list_of_seq A s n)) = (s m).
Axiom thm_LIST_OF_SEQ_EQ_NIL : forall (A : Type'), forall s : num -> A, forall n : num, ((list_of_seq A s n) = (NIL A)) = (n = (NUMERAL _0)).
Axiom thm_MONO_ALL : forall (A : Type') (P : A -> Prop) (Q : A -> Prop) (l : list A), (forall x : A, (P x) -> Q x) -> (ALL A P l) -> ALL A Q l.
Axiom thm_MONO_ALL2 : forall (A B : Type') (P : A -> B -> Prop) (Q : A -> B -> Prop) (l : list A) (l' : list B), (forall x : A, forall y : B, (P x y) -> Q x y) -> (ALL2 A B P l l') -> ALL2 A B Q l l'.
Axiom thm_char_INDUCT : forall P : char -> Prop, (forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, P (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) -> forall x : char, P x.
Axiom thm_char_RECURSION : forall (Z' : Type'), forall f : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Z', exists fn : char -> Z', forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, (fn (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) = (f a0 a1 a2 a3 a4 a5 a6 a7).
Axiom thm_dist : forall n : num, forall m : num, (dist (@pair num num m n)) = (add (minus m n) (minus n m)).
Axiom thm_DIST_REFL : forall n : num, (dist (@pair num num n n)) = (NUMERAL _0).
Axiom thm_DIST_LZERO : forall n : num, (dist (@pair num num (NUMERAL _0) n)) = n.
Axiom thm_DIST_RZERO : forall n : num, (dist (@pair num num n (NUMERAL _0))) = n.
Axiom thm_DIST_SYM : forall m : num, forall n : num, (dist (@pair num num m n)) = (dist (@pair num num n m)).
Axiom thm_DIST_LADD : forall m : num, forall p : num, forall n : num, (dist (@pair num num (add m n) (add m p))) = (dist (@pair num num n p)).
Axiom thm_DIST_RADD : forall m : num, forall p : num, forall n : num, (dist (@pair num num (add m p) (add n p))) = (dist (@pair num num m n)).
Axiom thm_DIST_LADD_0 : forall m : num, forall n : num, (dist (@pair num num (add m n) m)) = n.
Axiom thm_DIST_RADD_0 : forall m : num, forall n : num, (dist (@pair num num m (add m n))) = n.
Axiom thm_DIST_LMUL : forall m : num, forall n : num, forall p : num, (mul m (dist (@pair num num n p))) = (dist (@pair num num (mul m n) (mul m p))).
Axiom thm_DIST_RMUL : forall m : num, forall n : num, forall p : num, (mul (dist (@pair num num m n)) p) = (dist (@pair num num (mul m p) (mul n p))).
Axiom thm_DIST_EQ_0 : forall m : num, forall n : num, ((dist (@pair num num m n)) = (NUMERAL _0)) = (m = n).
Axiom thm_DIST_ELIM_THM : forall (y : num) (x : num) (P : num -> Prop), (P (dist (@pair num num x y))) = (forall d : num, ((x = (add y d)) -> P d) /\ ((y = (add x d)) -> P d)).
Axiom thm_DIST_TRIANGLE_LE : forall m : num, forall n : num, forall p : num, forall q : num, (le (add (dist (@pair num num m n)) (dist (@pair num num n p))) q) -> le (dist (@pair num num m p)) q.
Axiom thm_DIST_TRIANGLES_LE : forall m : num, forall n : num, forall p : num, forall q : num, forall r : num, forall s : num, ((le (dist (@pair num num m n)) r) /\ (le (dist (@pair num num p q)) s)) -> le (dist (@pair num num m p)) (add (dist (@pair num num n q)) (add r s)).
Axiom thm_BOUNDS_LINEAR : forall A : num, forall B : num, forall C : num, (forall n : num, le (mul A n) (add (mul B n) C)) = (le A B).
Axiom thm_BOUNDS_LINEAR_0 : forall A : num, forall B : num, (forall n : num, le (mul A n) B) = (A = (NUMERAL _0)).
Axiom thm_BOUNDS_DIVIDED : forall P : num -> num, (exists B : num, forall n : num, le (P n) B) = (exists A : num, exists B : num, forall n : num, le (mul n (P n)) (add (mul A n) B)).
Axiom thm_BOUNDS_NOTZERO : forall P : num -> num -> num, forall A : num, forall B : num, (((P (NUMERAL _0) (NUMERAL _0)) = (NUMERAL _0)) /\ (forall m : num, forall n : num, le (P m n) (add (mul A (add m n)) B))) -> exists B' : num, forall m : num, forall n : num, le (P m n) (mul B' (add m n)).
Axiom thm_BOUNDS_IGNORE : forall P : num -> num, forall Q : num -> num, (exists B : num, forall i : num, le (P i) (add (Q i) B)) = (exists B : num, exists N' : num, forall i : num, (le N' i) -> le (P i) (add (Q i) B)).
Axiom thm_is_nadd : forall x : num -> num, (is_nadd x) = (exists B : num, forall m : num, forall n : num, le (dist (@pair num num (mul m (x n)) (mul n (x m)))) (mul B (add m n))).
Axiom thm_is_nadd_0 : is_nadd (fun n : num => NUMERAL _0).
Axiom thm_NADD_CAUCHY : forall x : nadd, exists B : num, forall m : num, forall n : num, le (dist (@pair num num (mul m (dest_nadd x n)) (mul n (dest_nadd x m)))) (mul B (add m n)).
Axiom thm_NADD_BOUND : forall x : nadd, exists A : num, exists B : num, forall n : num, le (dest_nadd x n) (add (mul A n) B).
Axiom thm_NADD_MULTIPLICATIVE : forall x : nadd, exists B : num, forall m : num, forall n : num, le (dist (@pair num num (dest_nadd x (mul m n)) (mul m (dest_nadd x n)))) (add (mul B m) B).
Axiom thm_NADD_ADDITIVE : forall x : nadd, exists B : num, forall m : num, forall n : num, le (dist (@pair num num (dest_nadd x (add m n)) (add (dest_nadd x m) (dest_nadd x n)))) B.
Axiom thm_NADD_SUC : forall x : nadd, exists B : num, forall n : num, le (dist (@pair num num (dest_nadd x (SUC n)) (dest_nadd x n))) B.
Axiom thm_NADD_DIST_LEMMA : forall x : nadd, exists B : num, forall m : num, forall n : num, le (dist (@pair num num (dest_nadd x (add m n)) (dest_nadd x m))) (mul B n).
Axiom thm_NADD_DIST : forall x : nadd, exists B : num, forall m : num, forall n : num, le (dist (@pair num num (dest_nadd x m) (dest_nadd x n))) (mul B (dist (@pair num num m n))).
Axiom thm_NADD_ALTMUL : forall x : nadd, forall y : nadd, exists A : num, exists B : num, forall n : num, le (dist (@pair num num (mul n (dest_nadd x (dest_nadd y n))) (mul (dest_nadd x n) (dest_nadd y n)))) (add (mul A n) B).
Axiom thm_nadd_eq : forall x : nadd, forall y : nadd, (nadd_eq x y) = (exists B : num, forall n : num, le (dist (@pair num num (dest_nadd x n) (dest_nadd y n))) B).
Axiom thm_NADD_EQ_REFL : forall x : nadd, nadd_eq x x.
Axiom thm_NADD_EQ_SYM : forall x : nadd, forall y : nadd, (nadd_eq x y) = (nadd_eq y x).
Axiom thm_NADD_EQ_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_eq x y) /\ (nadd_eq y z)) -> nadd_eq x z.
Axiom thm_nadd_of_num : forall k : num, (nadd_of_num k) = (mk_nadd (fun n : num => mul k n)).
Axiom thm_NADD_OF_NUM : forall k : num, (dest_nadd (nadd_of_num k)) = (fun n : num => mul k n).
Axiom thm_NADD_OF_NUM_WELLDEF : forall m : num, forall n : num, (m = n) -> nadd_eq (nadd_of_num m) (nadd_of_num n).
Axiom thm_NADD_OF_NUM_EQ : forall m : num, forall n : num, (nadd_eq (nadd_of_num m) (nadd_of_num n)) = (m = n).
Axiom thm_nadd_le : forall x : nadd, forall y : nadd, (nadd_le x y) = (exists B : num, forall n : num, le (dest_nadd x n) (add (dest_nadd y n) B)).
Axiom thm_NADD_LE_WELLDEF_LEMMA : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ ((nadd_eq y y') /\ (nadd_le x y))) -> nadd_le x' y'.
Axiom thm_NADD_LE_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> (nadd_le x y) = (nadd_le x' y').
Axiom thm_NADD_LE_REFL : forall x : nadd, nadd_le x x.
Axiom thm_NADD_LE_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_le x y) /\ (nadd_le y z)) -> nadd_le x z.
Axiom thm_NADD_LE_ANTISYM : forall x : nadd, forall y : nadd, ((nadd_le x y) /\ (nadd_le y x)) = (nadd_eq x y).
Axiom thm_NADD_LE_TOTAL_LEMMA : forall x : nadd, forall y : nadd, (~ (nadd_le x y)) -> forall B : num, exists n : num, (~ (n = (NUMERAL _0))) /\ (lt (add (dest_nadd y n) B) (dest_nadd x n)).
Axiom thm_NADD_LE_TOTAL : forall x : nadd, forall y : nadd, (nadd_le x y) \/ (nadd_le y x).
Axiom thm_NADD_ARCH : forall x : nadd, exists n : num, nadd_le x (nadd_of_num n).
Axiom thm_NADD_OF_NUM_LE : forall m : num, forall n : num, (nadd_le (nadd_of_num m) (nadd_of_num n)) = (le m n).
Axiom thm_nadd_add : forall x : nadd, forall y : nadd, (nadd_add x y) = (mk_nadd (fun n : num => add (dest_nadd x n) (dest_nadd y n))).
Axiom thm_NADD_ADD : forall x : nadd, forall y : nadd, (dest_nadd (nadd_add x y)) = (fun n : num => add (dest_nadd x n) (dest_nadd y n)).
Axiom thm_NADD_ADD_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_add x y) (nadd_add x' y').
Axiom thm_NADD_ADD_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_add x y) (nadd_add y x).
Axiom thm_NADD_ADD_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z).
Axiom thm_NADD_ADD_LID : forall x : nadd, nadd_eq (nadd_add (nadd_of_num (NUMERAL _0)) x) x.
Axiom thm_NADD_ADD_LCANCEL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_eq (nadd_add x y) (nadd_add x z)) -> nadd_eq y z.
Axiom thm_NADD_LE_ADD : forall x : nadd, forall y : nadd, nadd_le x (nadd_add x y).
Axiom thm_NADD_LE_EXISTS : forall x : nadd, forall y : nadd, (nadd_le x y) -> exists d : nadd, nadd_eq y (nadd_add x d).
Axiom thm_NADD_OF_NUM_ADD : forall m : num, forall n : num, nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (add m n)).
Axiom thm_nadd_mul : forall x : nadd, forall y : nadd, (nadd_mul x y) = (mk_nadd (fun n : num => dest_nadd x (dest_nadd y n))).
Axiom thm_NADD_MUL : forall x : nadd, forall y : nadd, (dest_nadd (nadd_mul x y)) = (fun n : num => dest_nadd x (dest_nadd y n)).
Axiom thm_NADD_MUL_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_mul x y) (nadd_mul y x).
Axiom thm_NADD_MUL_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z).
Axiom thm_NADD_MUL_LID : forall x : nadd, nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 _0))) x) x.
Axiom thm_NADD_LDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_add y z)) (nadd_add (nadd_mul x y) (nadd_mul x z)).
Axiom thm_NADD_MUL_WELLDEF_LEMMA : forall x : nadd, forall y : nadd, forall y' : nadd, (nadd_eq y y') -> nadd_eq (nadd_mul x y) (nadd_mul x y').
Axiom thm_NADD_MUL_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_mul x y) (nadd_mul x' y').
Axiom thm_NADD_OF_NUM_MUL : forall m : num, forall n : num, nadd_eq (nadd_mul (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (mul m n)).
Axiom thm_NADD_LE_0 : forall x : nadd, nadd_le (nadd_of_num (NUMERAL _0)) x.
Axiom thm_NADD_EQ_IMP_LE : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_le x y.
Axiom thm_NADD_LE_LMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le y z) -> nadd_le (nadd_mul x y) (nadd_mul x z).
Axiom thm_NADD_LE_RMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le x y) -> nadd_le (nadd_mul x z) (nadd_mul y z).
Axiom thm_NADD_LE_RADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x z) (nadd_add y z)) = (nadd_le x y).
Axiom thm_NADD_LE_LADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x y) (nadd_add x z)) = (nadd_le y z).
Axiom thm_NADD_RDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z)).
Axiom thm_NADD_ARCH_MULT : forall x : nadd, forall k : num, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists N' : num, nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N') x).
Axiom thm_NADD_ARCH_ZERO : forall x : nadd, forall k : nadd, (forall n : num, nadd_le (nadd_mul (nadd_of_num n) x) k) -> nadd_eq x (nadd_of_num (NUMERAL _0)).
Axiom thm_NADD_ARCH_LEMMA : forall x : nadd, forall y : nadd, forall z : nadd, (forall n : num, nadd_le (nadd_mul (nadd_of_num n) x) (nadd_add (nadd_mul (nadd_of_num n) y) z)) -> nadd_le x y.
Axiom thm_NADD_COMPLETE : forall P : nadd -> Prop, ((exists x : nadd, P x) /\ (exists M : nadd, forall x : nadd, (P x) -> nadd_le x M)) -> exists M : nadd, (forall x : nadd, (P x) -> nadd_le x M) /\ (forall M' : nadd, (forall x : nadd, (P x) -> nadd_le x M') -> nadd_le M M').
Axiom thm_NADD_UBOUND : forall x : nadd, exists B : num, exists N' : num, forall n : num, (le N' n) -> le (dest_nadd x n) (mul B n).
Axiom thm_NADD_NONZERO : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists N' : num, forall n : num, (le N' n) -> ~ ((dest_nadd x n) = (NUMERAL _0)).
Axiom thm_NADD_LBOUND : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists A : num, exists N' : num, forall n : num, (le N' n) -> le n (mul A (dest_nadd x n)).
Axiom thm_nadd_rinv : forall x : nadd, (nadd_rinv x) = (fun n : num => DIV (mul n n) (dest_nadd x n)).
Axiom thm_NADD_MUL_LINV_LEMMA0 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists A : num, exists B : num, forall n : num, le (nadd_rinv x n) (add (mul A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA1 : forall x : nadd, forall n : num, (~ ((dest_nadd x n) = (NUMERAL _0))) -> le (dist (@pair num num (mul (dest_nadd x n) (nadd_rinv x n)) (mul n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA2 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists N' : num, forall n : num, (le N' n) -> le (dist (@pair num num (mul (dest_nadd x n) (nadd_rinv x n)) (mul n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA3 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists N' : num, forall m : num, forall n : num, (le N' n) -> le (dist (@pair num num (mul m (mul (dest_nadd x m) (mul (dest_nadd x n) (nadd_rinv x n)))) (mul m (mul (dest_nadd x m) (mul n n))))) (mul m (mul (dest_nadd x m) (dest_nadd x n))).
Axiom thm_NADD_MUL_LINV_LEMMA4 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists N' : num, forall m : num, forall n : num, ((le N' m) /\ (le N' n)) -> le (mul (mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair num num (mul m (nadd_rinv x n)) (mul n (nadd_rinv x m))))) (add (mul (mul m n) (dist (@pair num num (mul m (dest_nadd x n)) (mul n (dest_nadd x m))))) (mul (mul (dest_nadd x m) (dest_nadd x n)) (add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA5 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists B : num, exists N' : num, forall m : num, forall n : num, ((le N' m) /\ (le N' n)) -> le (mul (mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair num num (mul m (nadd_rinv x n)) (mul n (nadd_rinv x m))))) (mul B (mul (mul m n) (add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA6 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists B : num, exists N' : num, forall m : num, forall n : num, ((le N' m) /\ (le N' n)) -> le (mul (mul m n) (dist (@pair num num (mul m (nadd_rinv x n)) (mul n (nadd_rinv x m))))) (mul B (mul (mul m n) (add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA7 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists B : num, exists N' : num, forall m : num, forall n : num, ((le N' m) /\ (le N' n)) -> le (dist (@pair num num (mul m (nadd_rinv x n)) (mul n (nadd_rinv x m)))) (mul B (add m n)).
Axiom thm_NADD_MUL_LINV_LEMMA7a : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> forall N' : num, exists A : num, exists B : num, forall m : num, forall n : num, (le m N') -> le (dist (@pair num num (mul m (nadd_rinv x n)) (mul n (nadd_rinv x m)))) (add (mul A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA8 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> exists B : num, forall m : num, forall n : num, le (dist (@pair num num (mul m (nadd_rinv x n)) (mul n (nadd_rinv x m)))) (mul B (add m n)).
Axiom thm_nadd_inv : forall x : nadd, (nadd_inv x) = (@COND nadd (nadd_eq x (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv x))).
Axiom thm_NADD_INV : forall x : nadd, (dest_nadd (nadd_inv x)) = (@COND (num -> num) (nadd_eq x (nadd_of_num (NUMERAL _0))) (fun n : num => NUMERAL _0) (nadd_rinv x)).
Axiom thm_NADD_MUL_LINV : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL _0)))) -> nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num (NUMERAL (BIT1 _0))).
Axiom thm_NADD_INV_0 : nadd_eq (nadd_inv (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)).
Axiom thm_NADD_INV_WELLDEF : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_eq (nadd_inv x) (nadd_inv y).
Axiom thm_HREAL_OF_NUM_EQ : forall m : num, forall n : num, ((hreal_of_num m) = (hreal_of_num n)) = (m = n).
Axiom thm_HREAL_OF_NUM_LE : forall m : num, forall n : num, (hreal_le (hreal_of_num m) (hreal_of_num n)) = (le m n).
Axiom thm_HREAL_OF_NUM_ADD : forall m : num, forall n : num, (hreal_add (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (add m n)).
Axiom thm_HREAL_OF_NUM_MUL : forall m : num, forall n : num, (hreal_mul (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (mul m n)).
Axiom thm_HREAL_LE_REFL : forall x : hreal, hreal_le x x.
Axiom thm_HREAL_LE_TRANS : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_le x y) /\ (hreal_le y z)) -> hreal_le x z.
Axiom thm_HREAL_LE_ANTISYM : forall x : hreal, forall y : hreal, ((hreal_le x y) /\ (hreal_le y x)) = (x = y).
Axiom thm_HREAL_LE_TOTAL : forall x : hreal, forall y : hreal, (hreal_le x y) \/ (hreal_le y x).
Axiom thm_HREAL_LE_ADD : forall x : hreal, forall y : hreal, hreal_le x (hreal_add x y).
Axiom thm_HREAL_LE_EXISTS : forall x : hreal, forall y : hreal, (hreal_le x y) -> exists d : hreal, y = (hreal_add x d).
Axiom thm_HREAL_ARCH : forall x : hreal, exists n : num, hreal_le x (hreal_of_num n).
Axiom thm_HREAL_ADD_SYM : forall x : hreal, forall y : hreal, (hreal_add x y) = (hreal_add y x).
Axiom thm_HREAL_ADD_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_add x (hreal_add y z)) = (hreal_add (hreal_add x y) z).
Axiom thm_HREAL_ADD_LID : forall x : hreal, (hreal_add (hreal_of_num (NUMERAL _0)) x) = x.
Axiom thm_HREAL_ADD_LCANCEL : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_add x y) = (hreal_add x z)) -> y = z.
Axiom thm_HREAL_MUL_SYM : forall x : hreal, forall y : hreal, (hreal_mul x y) = (hreal_mul y x).
Axiom thm_HREAL_MUL_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_mul y z)) = (hreal_mul (hreal_mul x y) z).
Axiom thm_HREAL_MUL_LID : forall x : hreal, (hreal_mul (hreal_of_num (NUMERAL (BIT1 _0))) x) = x.
Axiom thm_HREAL_ADD_LDISTRIB : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_add y z)) = (hreal_add (hreal_mul x y) (hreal_mul x z)).
Axiom thm_HREAL_MUL_LINV : forall x : hreal, (~ (x = (hreal_of_num (NUMERAL _0)))) -> (hreal_mul (hreal_inv x) x) = (hreal_of_num (NUMERAL (BIT1 _0))).
Axiom thm_HREAL_INV_0 : (hreal_inv (hreal_of_num (NUMERAL _0))) = (hreal_of_num (NUMERAL _0)).
Axiom thm_HREAL_LE_EXISTS_DEF : forall m : hreal, forall n : hreal, (hreal_le m n) = (exists d : hreal, n = (hreal_add m d)).
Axiom thm_HREAL_EQ_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m n) = (hreal_add m p)) = (n = p).
Axiom thm_HREAL_EQ_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m p) = (hreal_add n p)) = (m = n).
Axiom thm_HREAL_LE_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m n) (hreal_add m p)) = (hreal_le n p).
Axiom thm_HREAL_LE_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m p) (hreal_add n p)) = (hreal_le m n).
Axiom thm_HREAL_ADD_RID : forall n : hreal, (hreal_add n (hreal_of_num (NUMERAL _0))) = n.
Axiom thm_HREAL_ADD_RDISTRIB : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_mul (hreal_add m n) p) = (hreal_add (hreal_mul m p) (hreal_mul n p)).
Axiom thm_HREAL_MUL_LZERO : forall m : hreal, (hreal_mul (hreal_of_num (NUMERAL _0)) m) = (hreal_of_num (NUMERAL _0)).
Axiom thm_HREAL_MUL_RZERO : forall m : hreal, (hreal_mul m (hreal_of_num (NUMERAL _0))) = (hreal_of_num (NUMERAL _0)).
Axiom thm_HREAL_ADD_AC : forall (n : hreal) (m : hreal) (p : hreal), ((hreal_add m n) = (hreal_add n m)) /\ (((hreal_add (hreal_add m n) p) = (hreal_add m (hreal_add n p))) /\ ((hreal_add m (hreal_add n p)) = (hreal_add n (hreal_add m p)))).
Axiom thm_HREAL_LE_ADD2 : forall a : hreal, forall b : hreal, forall c : hreal, forall d : hreal, ((hreal_le a b) /\ (hreal_le c d)) -> hreal_le (hreal_add a c) (hreal_add b d).
Axiom thm_HREAL_LE_MUL_RCANCEL_IMP : forall a : hreal, forall b : hreal, forall c : hreal, (hreal_le a b) -> hreal_le (hreal_mul a c) (hreal_mul b c).
Axiom thm_treal_of_num : forall n : num, (treal_of_num n) = (@pair hreal hreal (hreal_of_num n) (hreal_of_num (NUMERAL _0))).
Axiom thm_treal_neg : forall y : hreal, forall x : hreal, (treal_neg (@pair hreal hreal x y)) = (@pair hreal hreal y x).
Axiom thm_treal_add : forall x1 : hreal, forall x2 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_add (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add x1 x2) (hreal_add y1 y2)).
Axiom thm_treal_mul : forall x1 : hreal, forall y2 : hreal, forall y1 : hreal, forall x2 : hreal, (treal_mul (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2)) (hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))).
Axiom thm_treal_le : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (hreal_le (hreal_add x1 y2) (hreal_add x2 y1)).
Axiom thm_treal_inv : forall y : hreal, forall x : hreal, (treal_inv (@pair hreal hreal x y)) = (@COND (prod hreal hreal) (x = y) (@pair hreal hreal (hreal_of_num (NUMERAL _0)) (hreal_of_num (NUMERAL _0))) (@COND (prod hreal hreal) (hreal_le y x) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => x = (hreal_add y d)))) (hreal_of_num (NUMERAL _0))) (@pair hreal hreal (hreal_of_num (NUMERAL _0)) (hreal_inv (@ε hreal (fun d : hreal => y = (hreal_add x d))))))).
Axiom thm_treal_eq : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Axiom thm_TREAL_EQ_REFL : forall x : prod hreal hreal, treal_eq x x.
Axiom thm_TREAL_EQ_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) = (treal_eq y x).
Axiom thm_TREAL_EQ_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_eq x y) /\ (treal_eq y z)) -> treal_eq x z.
Axiom thm_TREAL_EQ_AP : forall x : prod hreal hreal, forall y : prod hreal hreal, (x = y) -> treal_eq x y.
Axiom thm_TREAL_OF_NUM_EQ : forall m : num, forall n : num, (treal_eq (treal_of_num m) (treal_of_num n)) = (m = n).
Axiom thm_TREAL_OF_NUM_LE : forall m : num, forall n : num, (treal_le (treal_of_num m) (treal_of_num n)) = (le m n).
Axiom thm_TREAL_OF_NUM_ADD : forall m : num, forall n : num, treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (add m n)).
Axiom thm_TREAL_OF_NUM_MUL : forall m : num, forall n : num, treal_eq (treal_mul (treal_of_num m) (treal_of_num n)) (treal_of_num (mul m n)).
Axiom thm_TREAL_ADD_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_add x y) = (treal_add y x).
Axiom thm_TREAL_MUL_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_mul x y) = (treal_mul y x).
Axiom thm_TREAL_ADD_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_add x y) (treal_add y x).
Axiom thm_TREAL_ADD_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z).
Axiom thm_TREAL_ADD_LID : forall x : prod hreal hreal, treal_eq (treal_add (treal_of_num (NUMERAL _0)) x) x.
Axiom thm_TREAL_ADD_LINV : forall x : prod hreal hreal, treal_eq (treal_add (treal_neg x) x) (treal_of_num (NUMERAL _0)).
Axiom thm_TREAL_MUL_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_mul x y) (treal_mul y x).
Axiom thm_TREAL_MUL_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z).
Axiom thm_TREAL_MUL_LID : forall x : prod hreal hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 _0))) x) x.
Axiom thm_TREAL_ADD_LDISTRIB : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_add y z)) (treal_add (treal_mul x y) (treal_mul x z)).
Axiom thm_TREAL_LE_REFL : forall x : prod hreal hreal, treal_le x x.
Axiom thm_TREAL_LE_ANTISYM : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le x y) /\ (treal_le y x)) = (treal_eq x y).
Axiom thm_TREAL_LE_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_le x y) /\ (treal_le y z)) -> treal_le x z.
Axiom thm_TREAL_LE_TOTAL : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_le x y) \/ (treal_le y x).
Axiom thm_TREAL_LE_LADD_IMP : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, (treal_le y z) -> treal_le (treal_add x y) (treal_add x z).
Axiom thm_TREAL_LE_MUL : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL _0)) x) /\ (treal_le (treal_of_num (NUMERAL _0)) y)) -> treal_le (treal_of_num (NUMERAL _0)) (treal_mul x y).
Axiom thm_TREAL_INV_0 : treal_eq (treal_inv (treal_of_num (NUMERAL _0))) (treal_of_num (NUMERAL _0)).
Axiom thm_TREAL_MUL_LINV : forall x : prod hreal hreal, (~ (treal_eq x (treal_of_num (NUMERAL _0)))) -> treal_eq (treal_mul (treal_inv x) x) (treal_of_num (NUMERAL (BIT1 _0))).
Axiom thm_TREAL_OF_NUM_WELLDEF : forall m : num, forall n : num, (m = n) -> treal_eq (treal_of_num m) (treal_of_num n).
Axiom thm_TREAL_NEG_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_neg x1) (treal_neg x2).
Axiom thm_TREAL_ADD_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_add x1 y) (treal_add x2 y).
Axiom thm_TREAL_ADD_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_add x1 y1) (treal_add x2 y2).
Axiom thm_TREAL_MUL_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_mul x1 y) (treal_mul x2 y).
Axiom thm_TREAL_MUL_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_mul x1 y1) (treal_mul x2 y2).
Axiom thm_TREAL_EQ_IMP_LE : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_le x y.
Axiom thm_TREAL_LE_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> (treal_le x1 y1) = (treal_le x2 y2).
Axiom thm_TREAL_INV_WELLDEF : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_eq (treal_inv x) (treal_inv y).
Axiom thm_REAL_ADD_SYM : forall x : Real, forall y : Real, (real_add x y) = (real_add y x).
Axiom thm_REAL_ADD_ASSOC : forall x : Real, forall y : Real, forall z : Real, (real_add x (real_add y z)) = (real_add (real_add x y) z).
Axiom thm_REAL_ADD_LID : forall x : Real, (real_add (real_of_num (NUMERAL _0)) x) = x.
Axiom thm_REAL_ADD_LINV : forall x : Real, (real_add (real_neg x) x) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_MUL_SYM : forall x : Real, forall y : Real, (real_mul x y) = (real_mul y x).
Axiom thm_REAL_MUL_ASSOC : forall x : Real, forall y : Real, forall z : Real, (real_mul x (real_mul y z)) = (real_mul (real_mul x y) z).
Axiom thm_REAL_MUL_LID : forall x : Real, (real_mul (real_of_num (NUMERAL (BIT1 _0))) x) = x.
Axiom thm_REAL_ADD_LDISTRIB : forall x : Real, forall y : Real, forall z : Real, (real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z)).
Axiom thm_REAL_LE_REFL : forall x : Real, real_le x x.
Axiom thm_REAL_LE_ANTISYM : forall x : Real, forall y : Real, ((real_le x y) /\ (real_le y x)) = (x = y).
Axiom thm_REAL_LE_TRANS : forall x : Real, forall y : Real, forall z : Real, ((real_le x y) /\ (real_le y z)) -> real_le x z.
Axiom thm_REAL_LE_TOTAL : forall x : Real, forall y : Real, (real_le x y) \/ (real_le y x).
Axiom thm_REAL_LE_LADD_IMP : forall x : Real, forall y : Real, forall z : Real, (real_le y z) -> real_le (real_add x y) (real_add x z).
Axiom thm_REAL_LE_MUL : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le (real_of_num (NUMERAL _0)) y)) -> real_le (real_of_num (NUMERAL _0)) (real_mul x y).
Axiom thm_REAL_INV_0 : (real_inv (real_of_num (NUMERAL _0))) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_MUL_LINV : forall x : Real, (~ (x = (real_of_num (NUMERAL _0)))) -> (real_mul (real_inv x) x) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_OF_NUM_EQ : forall m : num, forall n : num, ((real_of_num m) = (real_of_num n)) = (m = n).
Axiom thm_REAL_OF_NUM_LE : forall m : num, forall n : num, (real_le (real_of_num m) (real_of_num n)) = (le m n).
Axiom thm_REAL_OF_NUM_ADD : forall m : num, forall n : num, (real_add (real_of_num m) (real_of_num n)) = (real_of_num (add m n)).
Axiom thm_REAL_OF_NUM_MUL : forall m : num, forall n : num, (real_mul (real_of_num m) (real_of_num n)) = (real_of_num (mul m n)).
Axiom thm_real_sub : forall x : Real, forall y : Real, (real_sub x y) = (real_add x (real_neg y)).
Axiom thm_real_lt : forall y : Real, forall x : Real, (real_lt x y) = (~ (real_le y x)).
Axiom thm_real_ge : forall y : Real, forall x : Real, (real_ge x y) = (real_le y x).
Axiom thm_real_gt : forall y : Real, forall x : Real, (real_gt x y) = (real_lt y x).
Axiom thm_real_abs : forall x : Real, (real_abs x) = (@COND Real (real_le (real_of_num (NUMERAL _0)) x) x (real_neg x)).
Axiom thm_real_pow : forall (x : Real), ((real_pow x (NUMERAL _0)) = (real_of_num (NUMERAL (BIT1 _0)))) /\ (forall n : num, (real_pow x (SUC n)) = (real_mul x (real_pow x n))).
Axiom thm_real_div : forall x : Real, forall y : Real, (real_div x y) = (real_mul x (real_inv y)).
Axiom thm_real_max : forall n : Real, forall m : Real, (real_max m n) = (@COND Real (real_le m n) n m).
Axiom thm_real_min : forall m : Real, forall n : Real, (real_min m n) = (@COND Real (real_le m n) m n).
Axiom thm_REAL_HREAL_LEMMA1 : exists r : hreal -> Real, (forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) = (exists y : hreal, x = (r y))) /\ (forall y : hreal, forall z : hreal, (hreal_le y z) = (real_le (r y) (r z))).
Axiom thm_REAL_HREAL_LEMMA2 : exists h : Real -> hreal, exists r : hreal -> Real, (forall x : hreal, (h (r x)) = x) /\ ((forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> (r (h x)) = x) /\ ((forall x : hreal, real_le (real_of_num (NUMERAL _0)) (r x)) /\ (forall x : hreal, forall y : hreal, (hreal_le x y) = (real_le (r x) (r y))))).
Axiom thm_REAL_COMPLETE_SOMEPOS : forall P : Real -> Prop, ((exists x : Real, (P x) /\ (real_le (real_of_num (NUMERAL _0)) x)) /\ (exists M : Real, forall x : Real, (P x) -> real_le x M)) -> exists M : Real, (forall x : Real, (P x) -> real_le x M) /\ (forall M' : Real, (forall x : Real, (P x) -> real_le x M') -> real_le M M').
Axiom thm_REAL_COMPLETE : forall P : Real -> Prop, ((exists x : Real, P x) /\ (exists M : Real, forall x : Real, (P x) -> real_le x M)) -> exists M : Real, (forall x : Real, (P x) -> real_le x M) /\ (forall M' : Real, (forall x : Real, (P x) -> real_le x M') -> real_le M M').
Axiom thm_REAL_ADD_AC : forall (n : Real) (m : Real) (p : Real), ((real_add m n) = (real_add n m)) /\ (((real_add (real_add m n) p) = (real_add m (real_add n p))) /\ ((real_add m (real_add n p)) = (real_add n (real_add m p)))).
Axiom thm_REAL_ADD_RINV : forall x : Real, (real_add x (real_neg x)) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_EQ_ADD_LCANCEL : forall x : Real, forall y : Real, forall z : Real, ((real_add x y) = (real_add x z)) = (y = z).
Axiom thm_REAL_EQ_ADD_RCANCEL : forall x : Real, forall y : Real, forall z : Real, ((real_add x z) = (real_add y z)) = (x = y).
Axiom thm_REAL_MUL_RZERO : forall x : Real, (real_mul x (real_of_num (NUMERAL _0))) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_MUL_LZERO : forall x : Real, (real_mul (real_of_num (NUMERAL _0)) x) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_NEG_NEG : forall x : Real, (real_neg (real_neg x)) = x.
Axiom thm_REAL_MUL_RNEG : forall x : Real, forall y : Real, (real_mul x (real_neg y)) = (real_neg (real_mul x y)).
Axiom thm_REAL_MUL_LNEG : forall x : Real, forall y : Real, (real_mul (real_neg x) y) = (real_neg (real_mul x y)).
Axiom thm_REAL_NEG_ADD : forall x : Real, forall y : Real, (real_neg (real_add x y)) = (real_add (real_neg x) (real_neg y)).
Axiom thm_REAL_ADD_RID : forall x : Real, (real_add x (real_of_num (NUMERAL _0))) = x.
Axiom thm_REAL_NEG_0 : (real_neg (real_of_num (NUMERAL _0))) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_LE_LNEG : forall x : Real, forall y : Real, (real_le (real_neg x) y) = (real_le (real_of_num (NUMERAL _0)) (real_add x y)).
Axiom thm_REAL_LE_NEG2 : forall x : Real, forall y : Real, (real_le (real_neg x) (real_neg y)) = (real_le y x).
Axiom thm_REAL_LE_RNEG : forall x : Real, forall y : Real, (real_le x (real_neg y)) = (real_le (real_add x y) (real_of_num (NUMERAL _0))).
Axiom thm_REAL_OF_NUM_POW : forall x : num, forall n : num, (real_pow (real_of_num x) n) = (real_of_num (EXP x n)).
Axiom thm_REAL_POW_NEG : forall x : Real, forall n : num, (real_pow (real_neg x) n) = (@COND Real (EVEN n) (real_pow x n) (real_neg (real_pow x n))).
Axiom thm_REAL_ABS_NUM : forall n : num, (real_abs (real_of_num n)) = (real_of_num n).
Axiom thm_REAL_ABS_NEG : forall x : Real, (real_abs (real_neg x)) = (real_abs x).
Axiom thm_REAL_LTE_TOTAL : forall x : Real, forall y : Real, (real_lt x y) \/ (real_le y x).
Axiom thm_REAL_LET_TOTAL : forall x : Real, forall y : Real, (real_le x y) \/ (real_lt y x).
Axiom thm_REAL_LT_IMP_LE : forall x : Real, forall y : Real, (real_lt x y) -> real_le x y.
Axiom thm_REAL_LTE_TRANS : forall x : Real, forall y : Real, forall z : Real, ((real_lt x y) /\ (real_le y z)) -> real_lt x z.
Axiom thm_REAL_LET_TRANS : forall x : Real, forall y : Real, forall z : Real, ((real_le x y) /\ (real_lt y z)) -> real_lt x z.
Axiom thm_REAL_LT_TRANS : forall x : Real, forall y : Real, forall z : Real, ((real_lt x y) /\ (real_lt y z)) -> real_lt x z.
Axiom thm_REAL_LE_ADD : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le (real_of_num (NUMERAL _0)) y)) -> real_le (real_of_num (NUMERAL _0)) (real_add x y).
Axiom thm_REAL_LTE_ANTISYM : forall x : Real, forall y : Real, ~ ((real_lt x y) /\ (real_le y x)).
Axiom thm_REAL_SUB_LE : forall x : Real, forall y : Real, (real_le (real_of_num (NUMERAL _0)) (real_sub x y)) = (real_le y x).
Axiom thm_REAL_NEG_SUB : forall x : Real, forall y : Real, (real_neg (real_sub x y)) = (real_sub y x).
Axiom thm_REAL_LE_LT : forall x : Real, forall y : Real, (real_le x y) = ((real_lt x y) \/ (x = y)).
Axiom thm_REAL_SUB_LT : forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL _0)) (real_sub x y)) = (real_lt y x).
Axiom thm_REAL_NOT_LT : forall x : Real, forall y : Real, (~ (real_lt x y)) = (real_le y x).
Axiom thm_REAL_SUB_0 : forall x : Real, forall y : Real, ((real_sub x y) = (real_of_num (NUMERAL _0))) = (x = y).
Axiom thm_REAL_LT_LE : forall x : Real, forall y : Real, (real_lt x y) = ((real_le x y) /\ (~ (x = y))).
Axiom thm_REAL_LT_REFL : forall x : Real, ~ (real_lt x x).
Axiom thm_REAL_LTE_ADD : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_le (real_of_num (NUMERAL _0)) y)) -> real_lt (real_of_num (NUMERAL _0)) (real_add x y).
Axiom thm_REAL_LET_ADD : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_of_num (NUMERAL _0)) y)) -> real_lt (real_of_num (NUMERAL _0)) (real_add x y).
Axiom thm_REAL_LT_ADD : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_of_num (NUMERAL _0)) y)) -> real_lt (real_of_num (NUMERAL _0)) (real_add x y).
Axiom thm_REAL_ENTIRE : forall x : Real, forall y : Real, ((real_mul x y) = (real_of_num (NUMERAL _0))) = ((x = (real_of_num (NUMERAL _0))) \/ (y = (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_LE_NEGTOTAL : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) \/ (real_le (real_of_num (NUMERAL _0)) (real_neg x)).
Axiom thm_REAL_LE_SQUARE : forall x : Real, real_le (real_of_num (NUMERAL _0)) (real_mul x x).
Axiom thm_REAL_MUL_RID : forall x : Real, (real_mul x (real_of_num (NUMERAL (BIT1 _0)))) = x.
Axiom thm_REAL_POW_2 : forall x : Real, (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) = (real_mul x x).
Axiom thm_REAL_POLY_CLAUSES : (forall x : Real, forall y : Real, forall z : Real, (real_add x (real_add y z)) = (real_add (real_add x y) z)) /\ ((forall x : Real, forall y : Real, (real_add x y) = (real_add y x)) /\ ((forall x : Real, (real_add (real_of_num (NUMERAL _0)) x) = x) /\ ((forall x : Real, forall y : Real, forall z : Real, (real_mul x (real_mul y z)) = (real_mul (real_mul x y) z)) /\ ((forall x : Real, forall y : Real, (real_mul x y) = (real_mul y x)) /\ ((forall x : Real, (real_mul (real_of_num (NUMERAL (BIT1 _0))) x) = x) /\ ((forall x : Real, (real_mul (real_of_num (NUMERAL _0)) x) = (real_of_num (NUMERAL _0))) /\ ((forall x : Real, forall y : Real, forall z : Real, (real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z))) /\ ((forall x : Real, (real_pow x (NUMERAL _0)) = (real_of_num (NUMERAL (BIT1 _0)))) /\ (forall x : Real, forall n : num, (real_pow x (SUC n)) = (real_mul x (real_pow x n))))))))))).
Axiom thm_REAL_POLY_NEG_CLAUSES : (forall x : Real, (real_neg x) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 _0)))) x)) /\ (forall x : Real, forall y : Real, (real_sub x y) = (real_add x (real_mul (real_neg (real_of_num (NUMERAL (BIT1 _0)))) y))).
Axiom thm_REAL_POS : forall n : num, real_le (real_of_num (NUMERAL _0)) (real_of_num n).
Axiom thm_REAL_LT_NZ : forall n : num, (~ ((real_of_num n) = (real_of_num (NUMERAL _0)))) = (real_lt (real_of_num (NUMERAL _0)) (real_of_num n)).
Axiom thm_REAL_POS_LT : forall n : num, real_lt (real_of_num (NUMERAL _0)) (real_of_num (SUC n)).
Axiom thm_REAL_OF_NUM_LT : forall m : num, forall n : num, (real_lt (real_of_num m) (real_of_num n)) = (lt m n).
Axiom thm_REAL_OF_NUM_GE : forall m : num, forall n : num, (real_ge (real_of_num m) (real_of_num n)) = (ge m n).
Axiom thm_REAL_OF_NUM_GT : forall m : num, forall n : num, (real_gt (real_of_num m) (real_of_num n)) = (gt m n).
Axiom thm_REAL_OF_NUM_MAX : forall m : num, forall n : num, (real_max (real_of_num m) (real_of_num n)) = (real_of_num (MAX m n)).
Axiom thm_REAL_OF_NUM_MIN : forall m : num, forall n : num, (real_min (real_of_num m) (real_of_num n)) = (real_of_num (MIN m n)).
Axiom thm_REAL_OF_NUM_SUC : forall n : num, (real_add (real_of_num n) (real_of_num (NUMERAL (BIT1 _0)))) = (real_of_num (SUC n)).
Axiom thm_REAL_OF_NUM_SUB : forall m : num, forall n : num, (le m n) -> (real_sub (real_of_num n) (real_of_num m)) = (real_of_num (minus n m)).
Axiom thm_REAL_OF_NUM_SUB_CASES : forall m : num, forall n : num, (real_sub (real_of_num m) (real_of_num n)) = (@COND Real (le n m) (real_of_num (minus m n)) (real_neg (real_of_num (minus n m)))).
Axiom thm_REAL_OF_NUM_CLAUSES : (forall m : num, forall n : num, ((real_of_num m) = (real_of_num n)) = (m = n)) /\ ((forall m : num, forall n : num, (real_ge (real_of_num m) (real_of_num n)) = (ge m n)) /\ ((forall m : num, forall n : num, (real_gt (real_of_num m) (real_of_num n)) = (gt m n)) /\ ((forall m : num, forall n : num, (real_le (real_of_num m) (real_of_num n)) = (le m n)) /\ ((forall m : num, forall n : num, (real_lt (real_of_num m) (real_of_num n)) = (lt m n)) /\ ((forall m : num, forall n : num, (real_max (real_of_num m) (real_of_num n)) = (real_of_num (MAX m n))) /\ ((forall m : num, forall n : num, (real_min (real_of_num m) (real_of_num n)) = (real_of_num (MIN m n))) /\ ((forall m : num, forall n : num, (real_add (real_of_num m) (real_of_num n)) = (real_of_num (add m n))) /\ ((forall m : num, forall n : num, (real_mul (real_of_num m) (real_of_num n)) = (real_of_num (mul m n))) /\ (forall x : num, forall n : num, (real_pow (real_of_num x) n) = (real_of_num (EXP x n))))))))))).
Axiom thm_REAL_MUL_AC : forall (n : Real) (m : Real) (p : Real), ((real_mul m n) = (real_mul n m)) /\ (((real_mul (real_mul m n) p) = (real_mul m (real_mul n p))) /\ ((real_mul m (real_mul n p)) = (real_mul n (real_mul m p)))).
Axiom thm_REAL_ADD_RDISTRIB : forall x : Real, forall y : Real, forall z : Real, (real_mul (real_add x y) z) = (real_add (real_mul x z) (real_mul y z)).
Axiom thm_REAL_LT_LADD_IMP : forall x : Real, forall y : Real, forall z : Real, (real_lt y z) -> real_lt (real_add x y) (real_add x z).
Axiom thm_REAL_LT_MUL : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_of_num (NUMERAL _0)) y)) -> real_lt (real_of_num (NUMERAL _0)) (real_mul x y).
Axiom thm_REAL_EQ_ADD_LCANCEL_0 : forall x : Real, forall y : Real, ((real_add x y) = x) = (y = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_EQ_ADD_RCANCEL_0 : forall x : Real, forall y : Real, ((real_add x y) = y) = (x = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_LNEG_UNIQ : forall x : Real, forall y : Real, ((real_add x y) = (real_of_num (NUMERAL _0))) = (x = (real_neg y)).
Axiom thm_REAL_RNEG_UNIQ : forall x : Real, forall y : Real, ((real_add x y) = (real_of_num (NUMERAL _0))) = (y = (real_neg x)).
Axiom thm_REAL_NEG_LMUL : forall x : Real, forall y : Real, (real_neg (real_mul x y)) = (real_mul (real_neg x) y).
Axiom thm_REAL_NEG_RMUL : forall x : Real, forall y : Real, (real_neg (real_mul x y)) = (real_mul x (real_neg y)).
Axiom thm_REAL_NEG_MUL2 : forall x : Real, forall y : Real, (real_mul (real_neg x) (real_neg y)) = (real_mul x y).
Axiom thm_REAL_LT_LADD : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_add x y) (real_add x z)) = (real_lt y z).
Axiom thm_REAL_LT_RADD : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_add x z) (real_add y z)) = (real_lt x y).
Axiom thm_REAL_LT_ANTISYM : forall x : Real, forall y : Real, ~ ((real_lt x y) /\ (real_lt y x)).
Axiom thm_REAL_LT_GT : forall x : Real, forall y : Real, (real_lt x y) -> ~ (real_lt y x).
Axiom thm_REAL_NOT_EQ : forall x : Real, forall y : Real, (~ (x = y)) = ((real_lt x y) \/ (real_lt y x)).
Axiom thm_REAL_NOT_LE : forall x : Real, forall y : Real, (~ (real_le x y)) = (real_lt y x).
Axiom thm_REAL_LET_ANTISYM : forall x : Real, forall y : Real, ~ ((real_le x y) /\ (real_lt y x)).
Axiom thm_REAL_NEG_LT0 : forall x : Real, (real_lt (real_neg x) (real_of_num (NUMERAL _0))) = (real_lt (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_NEG_GT0 : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) (real_neg x)) = (real_lt x (real_of_num (NUMERAL _0))).
Axiom thm_REAL_NEG_LE0 : forall x : Real, (real_le (real_neg x) (real_of_num (NUMERAL _0))) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_NEG_GE0 : forall x : Real, (real_le (real_of_num (NUMERAL _0)) (real_neg x)) = (real_le x (real_of_num (NUMERAL _0))).
Axiom thm_REAL_LT_TOTAL : forall x : Real, forall y : Real, (x = y) \/ ((real_lt x y) \/ (real_lt y x)).
Axiom thm_REAL_LT_NEGTOTAL : forall x : Real, (x = (real_of_num (NUMERAL _0))) \/ ((real_lt (real_of_num (NUMERAL _0)) x) \/ (real_lt (real_of_num (NUMERAL _0)) (real_neg x))).
Axiom thm_REAL_LE_01 : real_le (real_of_num (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_LT_01 : real_lt (real_of_num (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_LE_LADD : forall x : Real, forall y : Real, forall z : Real, (real_le (real_add x y) (real_add x z)) = (real_le y z).
Axiom thm_REAL_LE_RADD : forall x : Real, forall y : Real, forall z : Real, (real_le (real_add x z) (real_add y z)) = (real_le x y).
Axiom thm_REAL_LT_ADD2 : forall w : Real, forall x : Real, forall y : Real, forall z : Real, ((real_lt w x) /\ (real_lt y z)) -> real_lt (real_add w y) (real_add x z).
Axiom thm_REAL_LE_ADD2 : forall w : Real, forall x : Real, forall y : Real, forall z : Real, ((real_le w x) /\ (real_le y z)) -> real_le (real_add w y) (real_add x z).
Axiom thm_REAL_LT_LNEG : forall x : Real, forall y : Real, (real_lt (real_neg x) y) = (real_lt (real_of_num (NUMERAL _0)) (real_add x y)).
Axiom thm_REAL_LT_RNEG : forall x : Real, forall y : Real, (real_lt x (real_neg y)) = (real_lt (real_add x y) (real_of_num (NUMERAL _0))).
Axiom thm_REAL_LT_ADDNEG : forall x : Real, forall y : Real, forall z : Real, (real_lt y (real_add x (real_neg z))) = (real_lt (real_add y z) x).
Axiom thm_REAL_LT_ADDNEG2 : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_add x (real_neg y)) z) = (real_lt x (real_add z y)).
Axiom thm_REAL_LT_ADD1 : forall x : Real, forall y : Real, (real_le x y) -> real_lt x (real_add y (real_of_num (NUMERAL (BIT1 _0)))).
Axiom thm_REAL_SUB_ADD : forall x : Real, forall y : Real, (real_add (real_sub x y) y) = x.
Axiom thm_REAL_SUB_ADD2 : forall x : Real, forall y : Real, (real_add y (real_sub x y)) = x.
Axiom thm_REAL_SUB_REFL : forall x : Real, (real_sub x x) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_LE_DOUBLE : forall x : Real, (real_le (real_of_num (NUMERAL _0)) (real_add x x)) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_LE_NEGL : forall x : Real, (real_le (real_neg x) x) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_LE_NEGR : forall x : Real, (real_le x (real_neg x)) = (real_le x (real_of_num (NUMERAL _0))).
Axiom thm_REAL_NEG_EQ_0 : forall x : Real, ((real_neg x) = (real_of_num (NUMERAL _0))) = (x = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_ADD_SUB : forall x : Real, forall y : Real, (real_sub (real_add x y) x) = y.
Axiom thm_REAL_NEG_EQ : forall x : Real, forall y : Real, ((real_neg x) = y) = (x = (real_neg y)).
Axiom thm_REAL_NEG_MINUS1 : forall x : Real, (real_neg x) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 _0)))) x).
Axiom thm_REAL_LT_IMP_NE : forall x : Real, forall y : Real, (real_lt x y) -> ~ (x = y).
Axiom thm_REAL_LE_ADDR : forall x : Real, forall y : Real, (real_le x (real_add x y)) = (real_le (real_of_num (NUMERAL _0)) y).
Axiom thm_REAL_LE_ADDL : forall x : Real, forall y : Real, (real_le y (real_add x y)) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_LT_ADDR : forall x : Real, forall y : Real, (real_lt x (real_add x y)) = (real_lt (real_of_num (NUMERAL _0)) y).
Axiom thm_REAL_LT_ADDL : forall x : Real, forall y : Real, (real_lt y (real_add x y)) = (real_lt (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_SUB_SUB : forall x : Real, forall y : Real, (real_sub (real_sub x y) x) = (real_neg y).
Axiom thm_REAL_LT_ADD_SUB : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_add x y) z) = (real_lt x (real_sub z y)).
Axiom thm_REAL_LT_SUB_RADD : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_sub x y) z) = (real_lt x (real_add z y)).
Axiom thm_REAL_LT_SUB_LADD : forall x : Real, forall y : Real, forall z : Real, (real_lt x (real_sub y z)) = (real_lt (real_add x z) y).
Axiom thm_REAL_LE_SUB_LADD : forall x : Real, forall y : Real, forall z : Real, (real_le x (real_sub y z)) = (real_le (real_add x z) y).
Axiom thm_REAL_LE_SUB_RADD : forall x : Real, forall y : Real, forall z : Real, (real_le (real_sub x y) z) = (real_le x (real_add z y)).
Axiom thm_REAL_ADD2_SUB2 : forall a : Real, forall b : Real, forall c : Real, forall d : Real, (real_sub (real_add a b) (real_add c d)) = (real_add (real_sub a c) (real_sub b d)).
Axiom thm_REAL_SUB_LZERO : forall x : Real, (real_sub (real_of_num (NUMERAL _0)) x) = (real_neg x).
Axiom thm_REAL_SUB_RZERO : forall x : Real, (real_sub x (real_of_num (NUMERAL _0))) = x.
Axiom thm_REAL_LET_ADD2 : forall w : Real, forall x : Real, forall y : Real, forall z : Real, ((real_le w x) /\ (real_lt y z)) -> real_lt (real_add w y) (real_add x z).
Axiom thm_REAL_LTE_ADD2 : forall w : Real, forall x : Real, forall y : Real, forall z : Real, ((real_lt w x) /\ (real_le y z)) -> real_lt (real_add w y) (real_add x z).
Axiom thm_REAL_SUB_LNEG : forall x : Real, forall y : Real, (real_sub (real_neg x) y) = (real_neg (real_add x y)).
Axiom thm_REAL_SUB_RNEG : forall x : Real, forall y : Real, (real_sub x (real_neg y)) = (real_add x y).
Axiom thm_REAL_SUB_NEG2 : forall x : Real, forall y : Real, (real_sub (real_neg x) (real_neg y)) = (real_sub y x).
Axiom thm_REAL_SUB_TRIANGLE : forall a : Real, forall b : Real, forall c : Real, (real_add (real_sub a b) (real_sub b c)) = (real_sub a c).
Axiom thm_REAL_EQ_SUB_LADD : forall x : Real, forall y : Real, forall z : Real, (x = (real_sub y z)) = ((real_add x z) = y).
Axiom thm_REAL_EQ_SUB_RADD : forall x : Real, forall y : Real, forall z : Real, ((real_sub x y) = z) = (x = (real_add z y)).
Axiom thm_REAL_SUB_SUB2 : forall x : Real, forall y : Real, (real_sub x (real_sub x y)) = y.
Axiom thm_REAL_ADD_SUB2 : forall x : Real, forall y : Real, (real_sub x (real_add x y)) = (real_neg y).
Axiom thm_REAL_EQ_IMP_LE : forall x : Real, forall y : Real, (x = y) -> real_le x y.
Axiom thm_REAL_LT_IMP_NZ : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) x) -> ~ (x = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_DIFFSQ : forall x : Real, forall y : Real, (real_mul (real_add x y) (real_sub x y)) = (real_sub (real_mul x x) (real_mul y y)).
Axiom thm_REAL_EQ_NEG2 : forall x : Real, forall y : Real, ((real_neg x) = (real_neg y)) = (x = y).
Axiom thm_REAL_LT_NEG2 : forall x : Real, forall y : Real, (real_lt (real_neg x) (real_neg y)) = (real_lt y x).
Axiom thm_REAL_SUB_LDISTRIB : forall x : Real, forall y : Real, forall z : Real, (real_mul x (real_sub y z)) = (real_sub (real_mul x y) (real_mul x z)).
Axiom thm_REAL_SUB_RDISTRIB : forall x : Real, forall y : Real, forall z : Real, (real_mul (real_sub x y) z) = (real_sub (real_mul x z) (real_mul y z)).
Axiom thm_REAL_ABS_ZERO : forall x : Real, ((real_abs x) = (real_of_num (NUMERAL _0))) = (x = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_ABS_0 : (real_abs (real_of_num (NUMERAL _0))) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_ABS_1 : (real_abs (real_of_num (NUMERAL (BIT1 _0)))) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_ABS_TRIANGLE : forall x : Real, forall y : Real, real_le (real_abs (real_add x y)) (real_add (real_abs x) (real_abs y)).
Axiom thm_REAL_ABS_TRIANGLE_LE : forall x : Real, forall y : Real, forall z : Real, (real_le (real_add (real_abs x) (real_abs (real_sub y x))) z) -> real_le (real_abs y) z.
Axiom thm_REAL_ABS_TRIANGLE_LT : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_add (real_abs x) (real_abs (real_sub y x))) z) -> real_lt (real_abs y) z.
Axiom thm_REAL_ABS_POS : forall x : Real, real_le (real_of_num (NUMERAL _0)) (real_abs x).
Axiom thm_REAL_ABS_SUB : forall x : Real, forall y : Real, (real_abs (real_sub x y)) = (real_abs (real_sub y x)).
Axiom thm_REAL_ABS_NZ : forall x : Real, (~ (x = (real_of_num (NUMERAL _0)))) = (real_lt (real_of_num (NUMERAL _0)) (real_abs x)).
Axiom thm_REAL_ABS_ABS : forall x : Real, (real_abs (real_abs x)) = (real_abs x).
Axiom thm_REAL_ABS_LE : forall x : Real, real_le x (real_abs x).
Axiom thm_REAL_ABS_REFL : forall x : Real, ((real_abs x) = x) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_ABS_BETWEEN : forall x : Real, forall y : Real, forall d : Real, ((real_lt (real_of_num (NUMERAL _0)) d) /\ ((real_lt (real_sub x d) y) /\ (real_lt y (real_add x d)))) = (real_lt (real_abs (real_sub y x)) d).
Axiom thm_REAL_ABS_BOUND : forall x : Real, forall y : Real, forall d : Real, (real_lt (real_abs (real_sub x y)) d) -> real_lt y (real_add x d).
Axiom thm_REAL_ABS_STILLNZ : forall x : Real, forall y : Real, (real_lt (real_abs (real_sub x y)) (real_abs y)) -> ~ (x = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_ABS_CASES : forall x : Real, (x = (real_of_num (NUMERAL _0))) \/ (real_lt (real_of_num (NUMERAL _0)) (real_abs x)).
Axiom thm_REAL_ABS_BETWEEN1 : forall x : Real, forall y : Real, forall z : Real, ((real_lt x z) /\ (real_lt (real_abs (real_sub y x)) (real_sub z x))) -> real_lt y z.
Axiom thm_REAL_ABS_SIGN : forall x : Real, forall y : Real, (real_lt (real_abs (real_sub x y)) y) -> real_lt (real_of_num (NUMERAL _0)) x.
Axiom thm_REAL_ABS_SIGN2 : forall x : Real, forall y : Real, (real_lt (real_abs (real_sub x y)) (real_neg y)) -> real_lt x (real_of_num (NUMERAL _0)).
Axiom thm_REAL_ABS_CIRCLE : forall x : Real, forall y : Real, forall h : Real, (real_lt (real_abs h) (real_sub (real_abs y) (real_abs x))) -> real_lt (real_abs (real_add x h)) (real_abs y).
Axiom thm_REAL_SUB_ABS : forall x : Real, forall y : Real, real_le (real_sub (real_abs x) (real_abs y)) (real_abs (real_sub x y)).
Axiom thm_REAL_ABS_SUB_ABS : forall x : Real, forall y : Real, real_le (real_abs (real_sub (real_abs x) (real_abs y))) (real_abs (real_sub x y)).
Axiom thm_REAL_ABS_BETWEEN2 : forall x0 : Real, forall x : Real, forall y0 : Real, forall y : Real, ((real_lt x0 y0) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (real_abs (real_sub x x0))) (real_sub y0 x0)) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (real_abs (real_sub y y0))) (real_sub y0 x0)))) -> real_lt x y.
Axiom thm_REAL_ABS_BOUNDS : forall x : Real, forall k : Real, (real_le (real_abs x) k) = ((real_le (real_neg k) x) /\ (real_le x k)).
Axiom thm_REAL_BOUNDS_LE : forall x : Real, forall k : Real, ((real_le (real_neg k) x) /\ (real_le x k)) = (real_le (real_abs x) k).
Axiom thm_REAL_BOUNDS_LT : forall x : Real, forall k : Real, ((real_lt (real_neg k) x) /\ (real_lt x k)) = (real_lt (real_abs x) k).
Axiom thm_REAL_MIN_MAX : forall x : Real, forall y : Real, (real_min x y) = (real_neg (real_max (real_neg x) (real_neg y))).
Axiom thm_REAL_MAX_MIN : forall x : Real, forall y : Real, (real_max x y) = (real_neg (real_min (real_neg x) (real_neg y))).
Axiom thm_REAL_MAX_MAX : forall x : Real, forall y : Real, (real_le x (real_max x y)) /\ (real_le y (real_max x y)).
Axiom thm_REAL_MIN_MIN : forall x : Real, forall y : Real, (real_le (real_min x y) x) /\ (real_le (real_min x y) y).
Axiom thm_REAL_MAX_SYM : forall x : Real, forall y : Real, (real_max x y) = (real_max y x).
Axiom thm_REAL_MIN_SYM : forall x : Real, forall y : Real, (real_min x y) = (real_min y x).
Axiom thm_REAL_LE_MAX : forall x : Real, forall y : Real, forall z : Real, (real_le z (real_max x y)) = ((real_le z x) \/ (real_le z y)).
Axiom thm_REAL_LE_MIN : forall x : Real, forall y : Real, forall z : Real, (real_le z (real_min x y)) = ((real_le z x) /\ (real_le z y)).
Axiom thm_REAL_LT_MAX : forall x : Real, forall y : Real, forall z : Real, (real_lt z (real_max x y)) = ((real_lt z x) \/ (real_lt z y)).
Axiom thm_REAL_LT_MIN : forall x : Real, forall y : Real, forall z : Real, (real_lt z (real_min x y)) = ((real_lt z x) /\ (real_lt z y)).
Axiom thm_REAL_MAX_LE : forall x : Real, forall y : Real, forall z : Real, (real_le (real_max x y) z) = ((real_le x z) /\ (real_le y z)).
Axiom thm_REAL_MIN_LE : forall x : Real, forall y : Real, forall z : Real, (real_le (real_min x y) z) = ((real_le x z) \/ (real_le y z)).
Axiom thm_REAL_MAX_LT : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_max x y) z) = ((real_lt x z) /\ (real_lt y z)).
Axiom thm_REAL_MIN_LT : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_min x y) z) = ((real_lt x z) \/ (real_lt y z)).
Axiom thm_REAL_MAX_ASSOC : forall x : Real, forall y : Real, forall z : Real, (real_max x (real_max y z)) = (real_max (real_max x y) z).
Axiom thm_REAL_MIN_ASSOC : forall x : Real, forall y : Real, forall z : Real, (real_min x (real_min y z)) = (real_min (real_min x y) z).
Axiom thm_REAL_MAX_ACI : forall (z : Real) (x : Real) (y : Real), ((real_max x y) = (real_max y x)) /\ (((real_max (real_max x y) z) = (real_max x (real_max y z))) /\ (((real_max x (real_max y z)) = (real_max y (real_max x z))) /\ (((real_max x x) = x) /\ ((real_max x (real_max x y)) = (real_max x y))))).
Axiom thm_REAL_MIN_ACI : forall (z : Real) (x : Real) (y : Real), ((real_min x y) = (real_min y x)) /\ (((real_min (real_min x y) z) = (real_min x (real_min y z))) /\ (((real_min x (real_min y z)) = (real_min y (real_min x z))) /\ (((real_min x x) = x) /\ ((real_min x (real_min x y)) = (real_min x y))))).
Axiom thm_REAL_ABS_MUL : forall x : Real, forall y : Real, (real_abs (real_mul x y)) = (real_mul (real_abs x) (real_abs y)).
Axiom thm_REAL_POW_LE : forall x : Real, forall n : num, (real_le (real_of_num (NUMERAL _0)) x) -> real_le (real_of_num (NUMERAL _0)) (real_pow x n).
Axiom thm_REAL_POW_LT : forall x : Real, forall n : num, (real_lt (real_of_num (NUMERAL _0)) x) -> real_lt (real_of_num (NUMERAL _0)) (real_pow x n).
Axiom thm_REAL_ABS_POW : forall x : Real, forall n : num, (real_abs (real_pow x n)) = (real_pow (real_abs x) n).
Axiom thm_REAL_LE_LMUL : forall x : Real, forall y : Real, forall z : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le y z)) -> real_le (real_mul x y) (real_mul x z).
Axiom thm_REAL_LE_RMUL : forall x : Real, forall y : Real, forall z : Real, ((real_le x y) /\ (real_le (real_of_num (NUMERAL _0)) z)) -> real_le (real_mul x z) (real_mul y z).
Axiom thm_REAL_LT_LMUL : forall x : Real, forall y : Real, forall z : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt y z)) -> real_lt (real_mul x y) (real_mul x z).
Axiom thm_REAL_LT_RMUL : forall x : Real, forall y : Real, forall z : Real, ((real_lt x y) /\ (real_lt (real_of_num (NUMERAL _0)) z)) -> real_lt (real_mul x z) (real_mul y z).
Axiom thm_REAL_EQ_MUL_LCANCEL : forall x : Real, forall y : Real, forall z : Real, ((real_mul x y) = (real_mul x z)) = ((x = (real_of_num (NUMERAL _0))) \/ (y = z)).
Axiom thm_REAL_EQ_MUL_RCANCEL : forall x : Real, forall y : Real, forall z : Real, ((real_mul x z) = (real_mul y z)) = ((x = y) \/ (z = (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_MUL_LINV_UNIQ : forall x : Real, forall y : Real, ((real_mul x y) = (real_of_num (NUMERAL (BIT1 _0)))) -> (real_inv y) = x.
Axiom thm_REAL_MUL_RINV_UNIQ : forall x : Real, forall y : Real, ((real_mul x y) = (real_of_num (NUMERAL (BIT1 _0)))) -> (real_inv x) = y.
Axiom thm_REAL_INV_INV : forall x : Real, (real_inv (real_inv x)) = x.
Axiom thm_REAL_EQ_INV2 : forall x : Real, forall y : Real, ((real_inv x) = (real_inv y)) = (x = y).
Axiom thm_REAL_INV_EQ_0 : forall x : Real, ((real_inv x) = (real_of_num (NUMERAL _0))) = (x = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_LT_INV : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) x) -> real_lt (real_of_num (NUMERAL _0)) (real_inv x).
Axiom thm_REAL_LT_INV_EQ : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) (real_inv x)) = (real_lt (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_INV_NEG : forall x : Real, (real_inv (real_neg x)) = (real_neg (real_inv x)).
Axiom thm_REAL_LE_INV_EQ : forall x : Real, (real_le (real_of_num (NUMERAL _0)) (real_inv x)) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_LE_INV : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> real_le (real_of_num (NUMERAL _0)) (real_inv x).
Axiom thm_REAL_MUL_RINV : forall x : Real, (~ (x = (real_of_num (NUMERAL _0)))) -> (real_mul x (real_inv x)) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_INV_1 : (real_inv (real_of_num (NUMERAL (BIT1 _0)))) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_INV_EQ_1 : forall x : Real, ((real_inv x) = (real_of_num (NUMERAL (BIT1 _0)))) = (x = (real_of_num (NUMERAL (BIT1 _0)))).
Axiom thm_REAL_DIV_1 : forall x : Real, (real_div x (real_of_num (NUMERAL (BIT1 _0)))) = x.
Axiom thm_REAL_DIV_REFL : forall x : Real, (~ (x = (real_of_num (NUMERAL _0)))) -> (real_div x x) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_DIV_RMUL : forall x : Real, forall y : Real, (~ (y = (real_of_num (NUMERAL _0)))) -> (real_mul (real_div x y) y) = x.
Axiom thm_REAL_DIV_LMUL : forall x : Real, forall y : Real, (~ (y = (real_of_num (NUMERAL _0)))) -> (real_mul y (real_div x y)) = x.
Axiom thm_REAL_DIV_EQ_1 : forall x : Real, forall y : Real, ((real_div x y) = (real_of_num (NUMERAL (BIT1 _0)))) = ((x = y) /\ ((~ (x = (real_of_num (NUMERAL _0)))) /\ (~ (y = (real_of_num (NUMERAL _0)))))).
Axiom thm_REAL_ABS_INV : forall x : Real, (real_abs (real_inv x)) = (real_inv (real_abs x)).
Axiom thm_REAL_ABS_DIV : forall x : Real, forall y : Real, (real_abs (real_div x y)) = (real_div (real_abs x) (real_abs y)).
Axiom thm_REAL_INV_MUL : forall x : Real, forall y : Real, (real_inv (real_mul x y)) = (real_mul (real_inv x) (real_inv y)).
Axiom thm_REAL_INV_DIV : forall x : Real, forall y : Real, (real_inv (real_div x y)) = (real_div y x).
Axiom thm_REAL_POW_MUL : forall x : Real, forall y : Real, forall n : num, (real_pow (real_mul x y) n) = (real_mul (real_pow x n) (real_pow y n)).
Axiom thm_REAL_POW_INV : forall x : Real, forall n : num, (real_pow (real_inv x) n) = (real_inv (real_pow x n)).
Axiom thm_REAL_INV_POW : forall x : Real, forall n : num, (real_inv (real_pow x n)) = (real_pow (real_inv x) n).
Axiom thm_REAL_POW_DIV : forall x : Real, forall y : Real, forall n : num, (real_pow (real_div x y) n) = (real_div (real_pow x n) (real_pow y n)).
Axiom thm_REAL_DIV_EQ_0 : forall x : Real, forall y : Real, ((real_div x y) = (real_of_num (NUMERAL _0))) = ((x = (real_of_num (NUMERAL _0))) \/ (y = (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_POW_ADD : forall x : Real, forall m : num, forall n : num, (real_pow x (add m n)) = (real_mul (real_pow x m) (real_pow x n)).
Axiom thm_REAL_POW_NZ : forall x : Real, forall n : num, (~ (x = (real_of_num (NUMERAL _0)))) -> ~ ((real_pow x n) = (real_of_num (NUMERAL _0))).
Axiom thm_REAL_POW_SUB : forall x : Real, forall m : num, forall n : num, ((~ (x = (real_of_num (NUMERAL _0)))) /\ (le m n)) -> (real_pow x (minus n m)) = (real_div (real_pow x n) (real_pow x m)).
Axiom thm_REAL_LT_LCANCEL_IMP : forall x : Real, forall y : Real, forall z : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_mul x y) (real_mul x z))) -> real_lt y z.
Axiom thm_REAL_LT_RCANCEL_IMP : forall x : Real, forall y : Real, forall z : Real, ((real_lt (real_of_num (NUMERAL _0)) z) /\ (real_lt (real_mul x z) (real_mul y z))) -> real_lt x y.
Axiom thm_REAL_LE_LCANCEL_IMP : forall x : Real, forall y : Real, forall z : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_le (real_mul x y) (real_mul x z))) -> real_le y z.
Axiom thm_REAL_LE_RCANCEL_IMP : forall x : Real, forall y : Real, forall z : Real, ((real_lt (real_of_num (NUMERAL _0)) z) /\ (real_le (real_mul x z) (real_mul y z))) -> real_le x y.
Axiom thm_REAL_LE_RMUL_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_le (real_mul x z) (real_mul y z)) = (real_le x y).
Axiom thm_REAL_LE_LMUL_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_le (real_mul z x) (real_mul z y)) = (real_le x y).
Axiom thm_REAL_LT_RMUL_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_lt (real_mul x z) (real_mul y z)) = (real_lt x y).
Axiom thm_REAL_LT_LMUL_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_lt (real_mul z x) (real_mul z y)) = (real_lt x y).
Axiom thm_REAL_LE_MUL_EQ : (forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL _0)) x) -> (real_le (real_of_num (NUMERAL _0)) (real_mul x y)) = (real_le (real_of_num (NUMERAL _0)) y)) /\ (forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL _0)) y) -> (real_le (real_of_num (NUMERAL _0)) (real_mul x y)) = (real_le (real_of_num (NUMERAL _0)) x)).
Axiom thm_REAL_LT_MUL_EQ : (forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL _0)) x) -> (real_lt (real_of_num (NUMERAL _0)) (real_mul x y)) = (real_lt (real_of_num (NUMERAL _0)) y)) /\ (forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL _0)) y) -> (real_lt (real_of_num (NUMERAL _0)) (real_mul x y)) = (real_lt (real_of_num (NUMERAL _0)) x)).
Axiom thm_REAL_MUL_POS_LT : forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL _0)) (real_mul x y)) = (((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_of_num (NUMERAL _0)) y)) \/ ((real_lt x (real_of_num (NUMERAL _0))) /\ (real_lt y (real_of_num (NUMERAL _0))))).
Axiom thm_REAL_MUL_POS_LE : forall x : Real, forall y : Real, (real_le (real_of_num (NUMERAL _0)) (real_mul x y)) = ((x = (real_of_num (NUMERAL _0))) \/ ((y = (real_of_num (NUMERAL _0))) \/ (((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_of_num (NUMERAL _0)) y)) \/ ((real_lt x (real_of_num (NUMERAL _0))) /\ (real_lt y (real_of_num (NUMERAL _0))))))).
Axiom thm_REAL_LE_RDIV_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_le x (real_div y z)) = (real_le (real_mul x z) y).
Axiom thm_REAL_LE_LDIV_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_le (real_div x z) y) = (real_le x (real_mul y z)).
Axiom thm_REAL_LT_RDIV_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_lt x (real_div y z)) = (real_lt (real_mul x z) y).
Axiom thm_REAL_LT_LDIV_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_lt (real_div x z) y) = (real_lt x (real_mul y z)).
Axiom thm_REAL_EQ_RDIV_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (x = (real_div y z)) = ((real_mul x z) = y).
Axiom thm_REAL_EQ_LDIV_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> ((real_div x z) = y) = (x = (real_mul y z)).
Axiom thm_REAL_LT_DIV2_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_lt (real_div x z) (real_div y z)) = (real_lt x y).
Axiom thm_REAL_LE_DIV2_EQ : forall x : Real, forall y : Real, forall z : Real, (real_lt (real_of_num (NUMERAL _0)) z) -> (real_le (real_div x z) (real_div y z)) = (real_le x y).
Axiom thm_REAL_MUL_2 : forall x : Real, (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) x) = (real_add x x).
Axiom thm_REAL_POW_EQ_0 : forall x : Real, forall n : num, ((real_pow x n) = (real_of_num (NUMERAL _0))) = ((x = (real_of_num (NUMERAL _0))) /\ (~ (n = (NUMERAL _0)))).
Axiom thm_REAL_LE_MUL2 : forall w : Real, forall x : Real, forall y : Real, forall z : Real, ((real_le (real_of_num (NUMERAL _0)) w) /\ ((real_le w x) /\ ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_le y z)))) -> real_le (real_mul w y) (real_mul x z).
Axiom thm_REAL_LT_MUL2 : forall w : Real, forall x : Real, forall y : Real, forall z : Real, ((real_le (real_of_num (NUMERAL _0)) w) /\ ((real_lt w x) /\ ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_lt y z)))) -> real_lt (real_mul w y) (real_mul x z).
Axiom thm_REAL_LT_SQUARE : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) (real_mul x x)) = (~ (x = (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_POW_1 : forall x : Real, (real_pow x (NUMERAL (BIT1 _0))) = x.
Axiom thm_REAL_POW_ONE : forall n : num, (real_pow (real_of_num (NUMERAL (BIT1 _0))) n) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_LT_INV2 : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt x y)) -> real_lt (real_inv y) (real_inv x).
Axiom thm_REAL_LE_INV2 : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_le x y)) -> real_le (real_inv y) (real_inv x).
Axiom thm_REAL_LT_LINV : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) y) /\ (real_lt (real_inv y) x)) -> real_lt (real_inv x) y.
Axiom thm_REAL_LT_RINV : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt x (real_inv y))) -> real_lt y (real_inv x).
Axiom thm_REAL_LE_LINV : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) y) /\ (real_le (real_inv y) x)) -> real_le (real_inv x) y.
Axiom thm_REAL_LE_RINV : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_le x (real_inv y))) -> real_le y (real_inv x).
Axiom thm_REAL_INV_LE_1 : forall x : Real, (real_le (real_of_num (NUMERAL (BIT1 _0))) x) -> real_le (real_inv x) (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_INV_1_LE : forall x : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_le x (real_of_num (NUMERAL (BIT1 _0))))) -> real_le (real_of_num (NUMERAL (BIT1 _0))) (real_inv x).
Axiom thm_REAL_INV_LT_1 : forall x : Real, (real_lt (real_of_num (NUMERAL (BIT1 _0))) x) -> real_lt (real_inv x) (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_INV_1_LT : forall x : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt x (real_of_num (NUMERAL (BIT1 _0))))) -> real_lt (real_of_num (NUMERAL (BIT1 _0))) (real_inv x).
Axiom thm_REAL_SUB_INV : forall x : Real, forall y : Real, ((~ (x = (real_of_num (NUMERAL _0)))) /\ (~ (y = (real_of_num (NUMERAL _0))))) -> (real_sub (real_inv x) (real_inv y)) = (real_div (real_sub y x) (real_mul x y)).
Axiom thm_REAL_DOWN : forall d : Real, (real_lt (real_of_num (NUMERAL _0)) d) -> exists e : Real, (real_lt (real_of_num (NUMERAL _0)) e) /\ (real_lt e d).
Axiom thm_REAL_DOWN2 : forall d1 : Real, forall d2 : Real, ((real_lt (real_of_num (NUMERAL _0)) d1) /\ (real_lt (real_of_num (NUMERAL _0)) d2)) -> exists e : Real, (real_lt (real_of_num (NUMERAL _0)) e) /\ ((real_lt e d1) /\ (real_lt e d2)).
Axiom thm_REAL_POW_LE2 : forall n : num, forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le x y)) -> real_le (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LE_1 : forall n : num, forall x : Real, (real_le (real_of_num (NUMERAL (BIT1 _0))) x) -> real_le (real_of_num (NUMERAL (BIT1 _0))) (real_pow x n).
Axiom thm_REAL_POW_1_LE : forall n : num, forall x : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le x (real_of_num (NUMERAL (BIT1 _0))))) -> real_le (real_pow x n) (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_POW_MONO : forall m : num, forall n : num, forall x : Real, ((real_le (real_of_num (NUMERAL (BIT1 _0))) x) /\ (le m n)) -> real_le (real_pow x m) (real_pow x n).
Axiom thm_REAL_POW_LT2 : forall n : num, forall x : Real, forall y : Real, ((~ (n = (NUMERAL _0))) /\ ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_lt x y))) -> real_lt (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LT_1 : forall n : num, forall x : Real, ((~ (n = (NUMERAL _0))) /\ (real_lt (real_of_num (NUMERAL (BIT1 _0))) x)) -> real_lt (real_of_num (NUMERAL (BIT1 _0))) (real_pow x n).
Axiom thm_REAL_POW_1_LT : forall n : num, forall x : Real, ((~ (n = (NUMERAL _0))) /\ ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_lt x (real_of_num (NUMERAL (BIT1 _0)))))) -> real_lt (real_pow x n) (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_POW_MONO_LT : forall m : num, forall n : num, forall x : Real, ((real_lt (real_of_num (NUMERAL (BIT1 _0))) x) /\ (lt m n)) -> real_lt (real_pow x m) (real_pow x n).
Axiom thm_REAL_POW_POW : forall x : Real, forall m : num, forall n : num, (real_pow (real_pow x m) n) = (real_pow x (mul m n)).
Axiom thm_REAL_EQ_RCANCEL_IMP : forall x : Real, forall y : Real, forall z : Real, ((~ (z = (real_of_num (NUMERAL _0)))) /\ ((real_mul x z) = (real_mul y z))) -> x = y.
Axiom thm_REAL_EQ_LCANCEL_IMP : forall x : Real, forall y : Real, forall z : Real, ((~ (z = (real_of_num (NUMERAL _0)))) /\ ((real_mul z x) = (real_mul z y))) -> x = y.
Axiom thm_REAL_LT_DIV : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) x) /\ (real_lt (real_of_num (NUMERAL _0)) y)) -> real_lt (real_of_num (NUMERAL _0)) (real_div x y).
Axiom thm_REAL_LE_DIV : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le (real_of_num (NUMERAL _0)) y)) -> real_le (real_of_num (NUMERAL _0)) (real_div x y).
Axiom thm_REAL_DIV_POW2 : forall x : Real, forall m : num, forall n : num, (~ (x = (real_of_num (NUMERAL _0)))) -> (real_div (real_pow x m) (real_pow x n)) = (@COND Real (le n m) (real_pow x (minus m n)) (real_inv (real_pow x (minus n m)))).
Axiom thm_REAL_DIV_POW2_ALT : forall x : Real, forall m : num, forall n : num, (~ (x = (real_of_num (NUMERAL _0)))) -> (real_div (real_pow x m) (real_pow x n)) = (@COND Real (lt n m) (real_pow x (minus m n)) (real_inv (real_pow x (minus n m)))).
Axiom thm_REAL_LT_POW2 : forall n : num, real_lt (real_of_num (NUMERAL _0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) n).
Axiom thm_REAL_LE_POW2 : forall n : num, real_le (real_of_num (NUMERAL (BIT1 _0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) n).
Axiom thm_REAL_POW2_ABS : forall x : Real, (real_pow (real_abs x) (NUMERAL (BIT0 (BIT1 _0)))) = (real_pow x (NUMERAL (BIT0 (BIT1 _0)))).
Axiom thm_REAL_LE_SQUARE_ABS : forall x : Real, forall y : Real, (real_le (real_abs x) (real_abs y)) = (real_le (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) (real_pow y (NUMERAL (BIT0 (BIT1 _0))))).
Axiom thm_REAL_LT_SQUARE_ABS : forall x : Real, forall y : Real, (real_lt (real_abs x) (real_abs y)) = (real_lt (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) (real_pow y (NUMERAL (BIT0 (BIT1 _0))))).
Axiom thm_REAL_EQ_SQUARE_ABS : forall x : Real, forall y : Real, ((real_abs x) = (real_abs y)) = ((real_pow x (NUMERAL (BIT0 (BIT1 _0)))) = (real_pow y (NUMERAL (BIT0 (BIT1 _0))))).
Axiom thm_REAL_LE_POW_2 : forall x : Real, real_le (real_of_num (NUMERAL _0)) (real_pow x (NUMERAL (BIT0 (BIT1 _0)))).
Axiom thm_REAL_LT_POW_2 : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) (real_pow x (NUMERAL (BIT0 (BIT1 _0))))) = (~ (x = (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_SOS_EQ_0 : forall x : Real, forall y : Real, ((real_add (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) (real_pow y (NUMERAL (BIT0 (BIT1 _0))))) = (real_of_num (NUMERAL _0))) = ((x = (real_of_num (NUMERAL _0))) /\ (y = (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_POW_ZERO : forall n : num, (real_pow (real_of_num (NUMERAL _0)) n) = (@COND Real (n = (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0))) (real_of_num (NUMERAL _0))).
Axiom thm_REAL_POW_MONO_INV : forall m : num, forall n : num, forall x : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ ((real_le x (real_of_num (NUMERAL (BIT1 _0)))) /\ (le n m))) -> real_le (real_pow x m) (real_pow x n).
Axiom thm_REAL_POW_LE2_REV : forall n : num, forall x : Real, forall y : Real, ((~ (n = (NUMERAL _0))) /\ ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_le (real_pow x n) (real_pow y n)))) -> real_le x y.
Axiom thm_REAL_POW_LT2_REV : forall n : num, forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_lt (real_pow x n) (real_pow y n))) -> real_lt x y.
Axiom thm_REAL_POW_EQ : forall n : num, forall x : Real, forall y : Real, ((~ (n = (NUMERAL _0))) /\ ((real_le (real_of_num (NUMERAL _0)) x) /\ ((real_le (real_of_num (NUMERAL _0)) y) /\ ((real_pow x n) = (real_pow y n))))) -> x = y.
Axiom thm_REAL_POW_EQ_ABS : forall n : num, forall x : Real, forall y : Real, ((~ (n = (NUMERAL _0))) /\ ((real_pow x n) = (real_pow y n))) -> (real_abs x) = (real_abs y).
Axiom thm_REAL_POW_EQ_1_IMP : forall x : Real, forall n : num, ((~ (n = (NUMERAL _0))) /\ ((real_pow x n) = (real_of_num (NUMERAL (BIT1 _0))))) -> (real_abs x) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_REAL_POW_EQ_1 : forall x : Real, forall n : num, ((real_pow x n) = (real_of_num (NUMERAL (BIT1 _0)))) = ((((real_abs x) = (real_of_num (NUMERAL (BIT1 _0)))) /\ ((real_lt x (real_of_num (NUMERAL _0))) -> EVEN n)) \/ (n = (NUMERAL _0))).
Axiom thm_REAL_POW_LT2_ODD : forall n : num, forall x : Real, forall y : Real, ((real_lt x y) /\ (ODD n)) -> real_lt (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LE2_ODD : forall n : num, forall x : Real, forall y : Real, ((real_le x y) /\ (ODD n)) -> real_le (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LT2_ODD_EQ : forall n : num, forall x : Real, forall y : Real, (ODD n) -> (real_lt (real_pow x n) (real_pow y n)) = (real_lt x y).
Axiom thm_REAL_POW_LE2_ODD_EQ : forall n : num, forall x : Real, forall y : Real, (ODD n) -> (real_le (real_pow x n) (real_pow y n)) = (real_le x y).
Axiom thm_REAL_POW_EQ_ODD_EQ : forall n : num, forall x : Real, forall y : Real, (ODD n) -> ((real_pow x n) = (real_pow y n)) = (x = y).
Axiom thm_REAL_POW_EQ_ODD : forall n : num, forall x : Real, forall y : Real, ((ODD n) /\ ((real_pow x n) = (real_pow y n))) -> x = y.
Axiom thm_REAL_POW_EQ_EQ : forall n : num, forall x : Real, forall y : Real, ((real_pow x n) = (real_pow y n)) = (@COND Prop (EVEN n) ((n = (NUMERAL _0)) \/ ((real_abs x) = (real_abs y))) (x = y)).
Axiom thm_REAL_EVENPOW_ABS : forall x : Real, forall n : num, (EVEN n) -> (real_pow (real_abs x) n) = (real_pow x n).
Axiom thm_REAL_OF_NUM_MOD : forall m : num, forall n : num, (real_of_num (MOD m n)) = (real_sub (real_of_num m) (real_mul (real_of_num (DIV m n)) (real_of_num n))).
Axiom thm_REAL_OF_NUM_DIV : forall m : num, forall n : num, (real_of_num (DIV m n)) = (real_sub (real_div (real_of_num m) (real_of_num n)) (real_div (real_of_num (MOD m n)) (real_of_num n))).
Axiom thm_REAL_CONVEX_BOUND2_LT : forall (b : Real), forall x : Real, forall y : Real, forall a : Real, forall u : Real, forall v : Real, ((real_lt x a) /\ ((real_lt y b) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))) -> real_lt (real_add (real_mul u x) (real_mul v y)) (real_add (real_mul u a) (real_mul v b)).
Axiom thm_REAL_CONVEX_BOUND2_LE : forall (b : Real), forall x : Real, forall y : Real, forall a : Real, forall u : Real, forall v : Real, ((real_le x a) /\ ((real_le y b) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))) -> real_le (real_add (real_mul u x) (real_mul v y)) (real_add (real_mul u a) (real_mul v b)).
Axiom thm_REAL_CONVEX_BOUND_LT : forall x : Real, forall y : Real, forall a : Real, forall u : Real, forall v : Real, ((real_lt x a) /\ ((real_lt y a) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))) -> real_lt (real_add (real_mul u x) (real_mul v y)) a.
Axiom thm_REAL_CONVEX_BOUND_LE : forall x : Real, forall y : Real, forall a : Real, forall u : Real, forall v : Real, ((real_le x a) /\ ((real_le y a) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))) -> real_le (real_add (real_mul u x) (real_mul v y)) a.
Axiom thm_REAL_CONVEX_BOUND_GT : forall x : Real, forall y : Real, forall a : Real, forall u : Real, forall v : Real, ((real_lt a x) /\ ((real_lt a y) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))) -> real_lt a (real_add (real_mul u x) (real_mul v y)).
Axiom thm_REAL_CONVEX_BOUND_GE : forall x : Real, forall y : Real, forall a : Real, forall u : Real, forall v : Real, ((real_le a x) /\ ((real_le a y) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))) -> real_le a (real_add (real_mul u x) (real_mul v y)).
Axiom thm_REAL_CONVEX_BOUNDS_LE : forall x : Real, forall y : Real, forall a : Real, forall b : Real, forall u : Real, forall v : Real, ((real_le a x) /\ ((real_le x b) /\ ((real_le a y) /\ ((real_le y b) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))))) -> (real_le a (real_add (real_mul u x) (real_mul v y))) /\ (real_le (real_add (real_mul u x) (real_mul v y)) b).
Axiom thm_REAL_CONVEX_BOUNDS_LT : forall x : Real, forall y : Real, forall a : Real, forall b : Real, forall u : Real, forall v : Real, ((real_lt a x) /\ ((real_lt x b) /\ ((real_lt a y) /\ ((real_lt y b) /\ ((real_le (real_of_num (NUMERAL _0)) u) /\ ((real_le (real_of_num (NUMERAL _0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 _0)))))))))) -> (real_lt a (real_add (real_mul u x) (real_mul v y))) /\ (real_lt (real_add (real_mul u x) (real_mul v y)) b).
Axiom thm_REAL_ARCH_SIMPLE : forall x : Real, exists n : num, real_le x (real_of_num n).
Axiom thm_REAL_ARCH_LT : forall x : Real, exists n : num, real_lt x (real_of_num n).
Axiom thm_REAL_ARCH : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) x) -> forall y : Real, exists n : num, real_lt y (real_mul (real_of_num n) x).
Axiom thm_REAL_ARCH_INV : forall e : Real, (real_lt (real_of_num (NUMERAL _0)) e) = (exists n : num, (~ (n = (NUMERAL _0))) /\ ((real_lt (real_of_num (NUMERAL _0)) (real_inv (real_of_num n))) /\ (real_lt (real_inv (real_of_num n)) e))).
Axiom thm_REAL_POW_LBOUND : forall x : Real, forall n : num, (real_le (real_of_num (NUMERAL _0)) x) -> real_le (real_add (real_of_num (NUMERAL (BIT1 _0))) (real_mul (real_of_num n) x)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 _0))) x) n).
Axiom thm_REAL_ARCH_POW : forall x : Real, forall y : Real, (real_lt (real_of_num (NUMERAL (BIT1 _0))) x) -> exists n : num, real_lt y (real_pow x n).
Axiom thm_REAL_ARCH_POW2 : forall x : Real, exists n : num, real_lt x (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) n).
Axiom thm_REAL_ARCH_POW_INV : forall x : Real, forall y : Real, ((real_lt (real_of_num (NUMERAL _0)) y) /\ (real_lt x (real_of_num (NUMERAL (BIT1 _0))))) -> exists n : num, real_lt (real_pow x n) y.
Axiom thm_real_sgn : forall x : Real, (real_sgn x) = (@COND Real (real_lt (real_of_num (NUMERAL _0)) x) (real_of_num (NUMERAL (BIT1 _0))) (@COND Real (real_lt x (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0)))).
Axiom thm_REAL_SGN_0 : (real_sgn (real_of_num (NUMERAL _0))) = (real_of_num (NUMERAL _0)).
Axiom thm_REAL_SGN_NEG : forall x : Real, (real_sgn (real_neg x)) = (real_neg (real_sgn x)).
Axiom thm_REAL_SGN_ABS : forall x : Real, (real_mul (real_sgn x) (real_abs x)) = x.
Axiom thm_REAL_SGN_ABS_ALT : forall x : Real, (real_mul (real_sgn x) x) = (real_abs x).
Axiom thm_REAL_EQ_SGN_ABS : forall x : Real, forall y : Real, (x = y) = (((real_sgn x) = (real_sgn y)) /\ ((real_abs x) = (real_abs y))).
Axiom thm_REAL_ABS_SGN : forall x : Real, (real_abs (real_sgn x)) = (real_sgn (real_abs x)).
Axiom thm_REAL_SGN : forall x : Real, (real_sgn x) = (real_div x (real_abs x)).
Axiom thm_REAL_SGN_MUL : forall x : Real, forall y : Real, (real_sgn (real_mul x y)) = (real_mul (real_sgn x) (real_sgn y)).
Axiom thm_REAL_SGN_INV : forall x : Real, (real_sgn (real_inv x)) = (real_sgn x).
Axiom thm_REAL_SGN_DIV : forall x : Real, forall y : Real, (real_sgn (real_div x y)) = (real_div (real_sgn x) (real_sgn y)).
Axiom thm_REAL_SGN_EQ : (forall x : Real, ((real_sgn x) = (real_of_num (NUMERAL _0))) = (x = (real_of_num (NUMERAL _0)))) /\ ((forall x : Real, ((real_sgn x) = (real_of_num (NUMERAL (BIT1 _0)))) = (real_gt x (real_of_num (NUMERAL _0)))) /\ (forall x : Real, ((real_sgn x) = (real_neg (real_of_num (NUMERAL (BIT1 _0))))) = (real_lt x (real_of_num (NUMERAL _0))))).
Axiom thm_REAL_SGN_CASES : forall x : Real, ((real_sgn x) = (real_of_num (NUMERAL _0))) \/ (((real_sgn x) = (real_of_num (NUMERAL (BIT1 _0)))) \/ ((real_sgn x) = (real_neg (real_of_num (NUMERAL (BIT1 _0)))))).
Axiom thm_REAL_SGN_INEQS : (forall x : Real, (real_le (real_of_num (NUMERAL _0)) (real_sgn x)) = (real_le (real_of_num (NUMERAL _0)) x)) /\ ((forall x : Real, (real_lt (real_of_num (NUMERAL _0)) (real_sgn x)) = (real_lt (real_of_num (NUMERAL _0)) x)) /\ ((forall x : Real, (real_ge (real_of_num (NUMERAL _0)) (real_sgn x)) = (real_ge (real_of_num (NUMERAL _0)) x)) /\ ((forall x : Real, (real_gt (real_of_num (NUMERAL _0)) (real_sgn x)) = (real_gt (real_of_num (NUMERAL _0)) x)) /\ ((forall x : Real, ((real_of_num (NUMERAL _0)) = (real_sgn x)) = ((real_of_num (NUMERAL _0)) = x)) /\ ((forall x : Real, (real_le (real_sgn x) (real_of_num (NUMERAL _0))) = (real_le x (real_of_num (NUMERAL _0)))) /\ ((forall x : Real, (real_lt (real_sgn x) (real_of_num (NUMERAL _0))) = (real_lt x (real_of_num (NUMERAL _0)))) /\ ((forall x : Real, (real_ge (real_sgn x) (real_of_num (NUMERAL _0))) = (real_ge x (real_of_num (NUMERAL _0)))) /\ ((forall x : Real, (real_gt (real_sgn x) (real_of_num (NUMERAL _0))) = (real_gt x (real_of_num (NUMERAL _0)))) /\ (forall x : Real, ((real_sgn x) = (real_of_num (NUMERAL _0))) = (x = (real_of_num (NUMERAL _0)))))))))))).
Axiom thm_REAL_SGN_POW : forall x : Real, forall n : num, (real_sgn (real_pow x n)) = (real_pow (real_sgn x) n).
Axiom thm_REAL_SGN_POW_2 : forall x : Real, (real_sgn (real_pow x (NUMERAL (BIT0 (BIT1 _0))))) = (real_sgn (real_abs x)).
Axiom thm_REAL_SGN_REAL_SGN : forall x : Real, (real_sgn (real_sgn x)) = (real_sgn x).
Axiom thm_REAL_INV_SGN : forall x : Real, (real_inv (real_sgn x)) = (real_sgn x).
Axiom thm_REAL_SGN_EQ_INEQ : forall x : Real, forall y : Real, ((real_sgn x) = (real_sgn y)) = ((x = y) \/ (real_lt (real_abs (real_sub x y)) (real_max (real_abs x) (real_abs y)))).
Axiom thm_REAL_SGNS_EQ : forall x : Real, forall y : Real, ((real_sgn x) = (real_sgn y)) = (((x = (real_of_num (NUMERAL _0))) = (y = (real_of_num (NUMERAL _0)))) /\ (((real_gt x (real_of_num (NUMERAL _0))) = (real_gt y (real_of_num (NUMERAL _0)))) /\ ((real_lt x (real_of_num (NUMERAL _0))) = (real_lt y (real_of_num (NUMERAL _0)))))).
Axiom thm_REAL_SGNS_EQ_ALT : forall x : Real, forall y : Real, ((real_sgn x) = (real_sgn y)) = (((x = (real_of_num (NUMERAL _0))) -> y = (real_of_num (NUMERAL _0))) /\ (((real_gt x (real_of_num (NUMERAL _0))) -> real_gt y (real_of_num (NUMERAL _0))) /\ ((real_lt x (real_of_num (NUMERAL _0))) -> real_lt y (real_of_num (NUMERAL _0))))).
Axiom thm_REAL_WLOG_LE : forall (P : Real -> Real -> Prop), ((forall x : Real, forall y : Real, (P x y) = (P y x)) /\ (forall x : Real, forall y : Real, (real_le x y) -> P x y)) -> forall x : Real, forall y : Real, P x y.
Axiom thm_REAL_WLOG_LT : forall (P : Real -> Real -> Prop), ((forall x : Real, P x x) /\ ((forall x : Real, forall y : Real, (P x y) = (P y x)) /\ (forall x : Real, forall y : Real, (real_lt x y) -> P x y))) -> forall x : Real, forall y : Real, P x y.
Axiom thm_REAL_WLOG_LE_3 : forall P : Real -> Real -> Real -> Prop, ((forall x : Real, forall y : Real, forall z : Real, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : Real, forall y : Real, forall z : Real, ((real_le x y) /\ (real_le y z)) -> P x y z)) -> forall x : Real, forall y : Real, forall z : Real, P x y z.
Axiom thm_sqrt : forall x : Real, (sqrt x) = (@ε Real (fun y : Real => ((real_sgn y) = (real_sgn x)) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 _0)))) = (real_abs x)))).
Axiom thm_SQRT_UNIQUE : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) y) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 _0)))) = x)) -> (sqrt x) = y.
Axiom thm_POW_2_SQRT : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> (sqrt (real_pow x (NUMERAL (BIT0 (BIT1 _0))))) = x.
Axiom thm_SQRT_0 : (sqrt (real_of_num (NUMERAL _0))) = (real_of_num (NUMERAL _0)).
Axiom thm_SQRT_1 : (sqrt (real_of_num (NUMERAL (BIT1 _0)))) = (real_of_num (NUMERAL (BIT1 _0))).
Axiom thm_POW_2_SQRT_ABS : forall x : Real, (sqrt (real_pow x (NUMERAL (BIT0 (BIT1 _0))))) = (real_abs x).
Axiom thm_SQRT_WORKS_GEN : forall x : Real, ((real_sgn (sqrt x)) = (real_sgn x)) /\ ((real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 _0)))) = (real_abs x)).
Axiom thm_SQRT_UNIQUE_GEN : forall x : Real, forall y : Real, (((real_sgn y) = (real_sgn x)) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 _0)))) = (real_abs x))) -> (sqrt x) = y.
Axiom thm_SQRT_NEG : forall x : Real, (sqrt (real_neg x)) = (real_neg (sqrt x)).
Axiom thm_REAL_SGN_SQRT : forall x : Real, (real_sgn (sqrt x)) = (real_sgn x).
Axiom thm_SQRT_WORKS : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> (real_le (real_of_num (NUMERAL _0)) (sqrt x)) /\ ((real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 _0)))) = x).
Axiom thm_REAL_POS_EQ_SQUARE : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) = (exists y : Real, (real_pow y (NUMERAL (BIT0 (BIT1 _0)))) = x).
Axiom thm_SQRT_POS_LE : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> real_le (real_of_num (NUMERAL _0)) (sqrt x).
Axiom thm_SQRT_POW_2 : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> (real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 _0)))) = x.
Axiom thm_SQRT_POW2 : forall x : Real, ((real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 _0)))) = x) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_SQRT_MUL : forall x : Real, forall y : Real, (sqrt (real_mul x y)) = (real_mul (sqrt x) (sqrt y)).
Axiom thm_SQRT_INV : forall x : Real, (sqrt (real_inv x)) = (real_inv (sqrt x)).
Axiom thm_SQRT_DIV : forall x : Real, forall y : Real, (sqrt (real_div x y)) = (real_div (sqrt x) (sqrt y)).
Axiom thm_SQRT_LT_0 : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) (sqrt x)) = (real_lt (real_of_num (NUMERAL _0)) x).
Axiom thm_SQRT_EQ_0 : forall x : Real, ((sqrt x) = (real_of_num (NUMERAL _0))) = (x = (real_of_num (NUMERAL _0))).
Axiom thm_SQRT_LE_0 : forall x : Real, (real_le (real_of_num (NUMERAL _0)) (sqrt x)) = (real_le (real_of_num (NUMERAL _0)) x).
Axiom thm_REAL_ABS_SQRT : forall x : Real, (real_abs (sqrt x)) = (sqrt (real_abs x)).
Axiom thm_SQRT_MONO_LT : forall x : Real, forall y : Real, (real_lt x y) -> real_lt (sqrt x) (sqrt y).
Axiom thm_SQRT_MONO_LE : forall x : Real, forall y : Real, (real_le x y) -> real_le (sqrt x) (sqrt y).
Axiom thm_SQRT_MONO_LT_EQ : forall x : Real, forall y : Real, (real_lt (sqrt x) (sqrt y)) = (real_lt x y).
Axiom thm_SQRT_MONO_LE_EQ : forall x : Real, forall y : Real, (real_le (sqrt x) (sqrt y)) = (real_le x y).
Axiom thm_SQRT_INJ : forall x : Real, forall y : Real, ((sqrt x) = (sqrt y)) = (x = y).
Axiom thm_SQRT_EQ_1 : forall x : Real, ((sqrt x) = (real_of_num (NUMERAL (BIT1 _0)))) = (x = (real_of_num (NUMERAL (BIT1 _0)))).
Axiom thm_SQRT_POS_LT : forall x : Real, (real_lt (real_of_num (NUMERAL _0)) x) -> real_lt (real_of_num (NUMERAL _0)) (sqrt x).
Axiom thm_REAL_LE_LSQRT : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_le x (real_pow y (NUMERAL (BIT0 (BIT1 _0)))))) -> real_le (sqrt x) y.
Axiom thm_REAL_LE_RSQRT : forall x : Real, forall y : Real, (real_le (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) y) -> real_le x (sqrt y).
Axiom thm_REAL_LT_LSQRT : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_lt x (real_pow y (NUMERAL (BIT0 (BIT1 _0)))))) -> real_lt (sqrt x) y.
Axiom thm_REAL_LT_RSQRT : forall x : Real, forall y : Real, (real_lt (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) y) -> real_lt x (sqrt y).
Axiom thm_SQRT_EVEN_POW2 : forall n : num, (EVEN n) -> (sqrt (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) n)) = (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (DIV n (NUMERAL (BIT0 (BIT1 _0))))).
Axiom thm_REAL_DIV_SQRT : forall x : Real, (real_le (real_of_num (NUMERAL _0)) x) -> (real_div x (sqrt x)) = (sqrt x).
Axiom thm_REAL_RSQRT_LE : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ ((real_le (real_of_num (NUMERAL _0)) y) /\ (real_le x (sqrt y)))) -> real_le (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) y.
Axiom thm_REAL_LSQRT_LE : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le (sqrt x) y)) -> real_le x (real_pow y (NUMERAL (BIT0 (BIT1 _0)))).
Axiom thm_REAL_SQRT_POW_2 : forall x : Real, (real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 _0)))) = (real_abs x).
Axiom thm_REAL_ABS_LE_SQRT_POS : forall x : Real, forall y : Real, ((real_le (real_of_num (NUMERAL _0)) x) /\ (real_le (real_of_num (NUMERAL _0)) y)) -> real_le (real_abs (real_sub (sqrt x) (sqrt y))) (sqrt (real_abs (real_sub x y))).
Axiom thm_REAL_ABS_LE_SQRT : forall x : Real, forall y : Real, real_le (real_abs (real_sub (sqrt x) (sqrt y))) (sqrt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (real_abs (real_sub x y)))).
End terms.
