Goals and ideas in no particular order.
##### Translate the proof checks :  
Currently I only wrote an ocaml code to translate the terms and theorems files obtained with hol2dk.  
One could already be satisfied with the checking of the original proofs and assume that it is assurance of the correctness of the theorems on typeclasses.  
But it is also possible to simply add in the dependencies of all proof file a file containing one axiom per class.  
I would personally be fully satisfied with that, as universal quantifying and axiom assumption are logically the same.
##### Implicit arguments :
Since the objects are now implicitly depending on each other, explicit arguments with @ are no longer usable.  
To deal with that, I removed them as well as all implicit arguments of all objects.  
But it's a bit annoying to work with so I will probably have the assertion of implicit arguments appear at the end of the file.
##### Alignment commands :
Currently, to align HOL object x with Rocq object y, one needs for example to write  
``Lemma x_def_i : y=[...]``  
``Proof.``  
``[...]``  
``Qed.``  
``Instance x_i : x_Class := {| x_def := x_def_i |}.``  
``Canonical x_i.``  
I want to experiment with writing a Rocq plugin to simplify this in one command and for variants as well.  
This would also be a good place to include fully automatic alignments for inductive types and recursive functions.
##### Custom Search command :
No idea about feasibility and complexity. Have a possibility for a user to have a Search (and maybe also Check) command that would also fetch lemmas about the HOL Light object (so the field of the Class).  
For example, having Search N.succ also include results for SUC.
Another possibility would be having commands to derive theorems. Even though theorems are readily usable once mappings are correct (all transparent and canonical), maybe it would be better to derive theorems on the actual objects, so that they would directly appear in regular Search and Check command.
