/* Map from dk/lp symbols on the right to Coq expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Coq expressions. */

// primitive types
builtin "Type'" ≔ Set;
builtin "point" ≔ el;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;

// connectives
builtin "eq" ≔ =;

builtin "imp" ≔ ⇒;
builtin "imp_def" ≔ ⇒_def;

builtin "all" ≔ ∀;
builtin "all_def" ≔ ∀_def;

builtin "or" ≔ ∨;
builtin "or_def" ≔ ∨_def;

builtin "and" ≔ ∧;
builtin "and_def" ≔ ∧_def;

builtin "ex" ≔ ∃;
builtin "ex_def" ≔ ∃_def;

builtin "not" ≔ ¬;
builtin "not_def" ≔ ¬_def;

builtin "True" ≔ ⊤;
builtin "T_def" ≔ ⊤_def;

builtin "False" ≔ ⊥;
builtin "F_def" ≔ ⊥_def;

builtin "ex1" ≔ ∃₁;
builtin "ex1_def" ≔ ∃₁_def;

// natural deduction rules
builtin "Logic.I" ≔ ⊤ᵢ;
builtin "conj" ≔ ∧ᵢ;
builtin "proj1" ≔ ∧ₑ₁;
builtin "proj2" ≔ ∧ₑ₂;
builtin "or_intro1" ≔ ∨ᵢ₁;
builtin "or_intror" ≔ ∨ᵢ₂;
builtin "or_elim" ≔ ∨ₑ;
builtin "ex_intro" ≔ ∃ᵢ;
builtin "ex_elim" ≔ ∃ₑ;

// HOL-Light rules
builtin "REFL" ≔ REFL;
builtin "EQ_MP" ≔ EQ_MP;
builtin "MK_COMB" ≔ MK_COMB;
builtin "ssrfun.etrans" ≔ TRANS;
builtin "ssrfun.esym" ≔ SYM;

// HOL-Light axioms
builtin "ε" ≔ ε;
builtin "axiom_0" ≔ axiom_0;
builtin "axiom_1" ≔ axiom_1;
builtin "funext" ≔ fun_ext;
builtin "prop_ext" ≔ prop_ext;

// if then else
builtin "COND" ≔ COND;
builtin "COND_def" ≔ COND_def;

// product type
builtin "mk_pair" ≔ mk_pair;
builtin "mk_pair_def" ≔ mk_pair_def;
builtin "prod" ≔ prod;
builtin "ABS_prod" ≔ ABS_prod;
builtin "REP_prod" ≔ REP_prod;
builtin "axiom_4" ≔ axiom_4;
builtin "axiom_5" ≔ axiom_5;
builtin "pair" ≔ ̦‚;
builtin "pair_def" ≔ ̦‚_def;
builtin "fst" ≔ FST;
builtin "FST_def" ≔ FST_def;
builtin "snd" ≔ SND;
builtin "SND_def" ≔ SND_def;

// infinite type ind
builtin "ind" ≔ ind;
builtin "ONE_ONE" ≔ ONE_ONE;
builtin "ONE_ONE_def" ≔ ONE_ONE_def;
builtin "ONTO" ≔ ONTO;
builtin "ONTO_def" ≔ ONTO_def;
builtin "axiom_6" ≔ axiom_6;

