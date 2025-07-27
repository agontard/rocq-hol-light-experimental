# rocq-hol-light-experimental

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
Using the coercion asbool from Prop to bool, it is possible to casematch on Prop.
