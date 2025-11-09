Require Import mathcomp.classical.classical_sets HOLLight_Real_with_N.HOL_Light.
Section definitions.
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
End definitions.
