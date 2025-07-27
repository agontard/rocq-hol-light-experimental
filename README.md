# rocq-hol-light-experimental

This is an experimental version of [coq-hol-light](https://github.com/Deducteam/coq-hol-light) in which the translation is done with minimal mappings, to typeclasses, so that mappings can be done *afterwards* by instanciating the classes.  
The benefits are that mappings can easily be changed without having to retranslate or recheck the proofs, and that this way HOL Light theorems can be used directly for mappings as long as all objects appearing in them are already mapped.

Because of the size of the proofs of the multivariate library, this repository only currently contains the contents of the [coq-hol-light-real-with-N](https://github.com/Deducteam/coq-hol-light-real-with-N) library. Mappings are currently being changed to typeclass instances.

Check TODO for plans and ideas of features for this translation.

## Tools for classical logic
To fit HOL Light's logic, we require the following usual axioms of classical logic, from mathcomp-classical/boolp.

<img width="495" height="182" alt="image" src="https://github.com/user-attachments/assets/34ea7276-fde1-4ea7-821a-338094000f7d" />


We use these axioms often and thus provide multiple tools to reason with them more easily inside and/or outside ssreflect

### extensionalities  
For use inside ssreflect intro patterns :
- `` /` ``  : applies propositional and functional extensionality as much as possible and puts the resulting function arguments and hypotheses on top of the stack for named introduction.
- `` /n` ``   : where n is between 1 and 5, extracts exactly n arguments/hypotheses.
- `` /f` `` : same as `` /` `` but only functional extensionality, doesn't break propositional equalities.

The corresponding Ltac tactics are ext, ext n (for any integer n) and funext. example :  
``move=> a b c /f` x y /2` H t`` is the same as ``intros a b c ; funext ; intros x y ; ext 2 ; intros H t``.

### if ... then ... else ...
Using the coercion asbool from Prop to bool, it is possible to do pattern matching on Prop using an if-then-else pattern.

For use inside ssreflect intro patterns :
- `` /c` `` performs case analysis on an `if P then x else y` anywhere inside the goal. Produces two goals in which it is replaced by `x` and `y` respectively, with hypothesis `P` and `~P` respectively put on top of the stack for named introduction. Additionally simplifies all other if-then-else patterns over the same proposition.

New ssreflect simpl tactic, for use inside either an intro or rewrite tactic :
- `` /1= `` : replaces `if P then x else y` with `x` (resp. `y`) if "now easy" can prove `P` (resp. `~P`).

The corresponding Ltac tactics are if_intro and if_triv. example :  
``rewrite H /1= H' => /c` [-> | neq]`` is the same as ``rewrite H ; if_triv ; rewrite H' ; if_intro ; [intros -> | intro neq]``.

### rewriting a boolean view
Thanks to propositional extensionality, a reflection is actually an equality (lemma `reflect_eq` in asbool.v).  
We added the postfix notation "**" for `reflect_eq`, so one can do `rewrite H negP** H'`
