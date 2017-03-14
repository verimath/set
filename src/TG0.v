Set Implicit Arguments.

(*** preliminary Meta Theory assumptions ***) 
Require Export Prelim.

Module Type TG.

Parameter set : Type.

(** * Axioms of set theory **)

(** Finally, we add the primitive operators and axioms of Tarski-Grothendieck Set Theory (Zermelo-Fraenkel with Grothendieck Universes). ***)

(** In is the membership relation on i.  We use x :e y as notation to mean "x is a member of y" and x /:e y as notation for "x is not a member of y." **)
Parameter In : set -> set -> Prop.

Notation "x ':e' y" := (In x y) (at level 70).
Notation "x '/:e' y" := (~(In x y)) (at level 70).

(** Subq is the subset relation on set.  We use X c= Y as notation to mean "X is a subset of Y" and X /c= Y as notation for "X is not a subset of Y." **)

Definition Subq : set -> set -> Prop :=
fun X Y => forall x : set, x :e X -> x :e Y.

Notation "X 'c=' Y" := (Subq X Y) (at level 70).
Notation "X '/c=' Y" := (~(Subq X Y)) (at level 70).

(** Two sets are equal if they have the same elements. Equivalently, we can always prove two sets are equal by proving they are subsets of each other. **)

Axiom set_ext : forall X Y : set, X c= Y -> Y c= X -> X = Y.

(** Sets are formed iteratively, so we can prove properties about all sets by induction on membership.
Suppose P is a property of sets. If we can prove P holds for X from the inductive hypothesis that P holds for all member of X,
then P must hold for all sets. **)

Axiom In_ind : forall P : set -> Prop, (forall X : set, (forall x, x :e X -> P x) -> P X) -> forall X : set, P X.

(** Empty is the empty set. **)

Parameter Empty : set.

Axiom EmptyE : forall x : set, x /:e Empty.

(** Given two sets y and z, (UPair y z) is {y,z}. **)

Parameter UPair : set -> set -> set.

Axiom UPairI1 :
forall y z : set, y :e (UPair y z).

Axiom UPairI2 :
forall y z : set, z :e (UPair y z).

Axiom UPairE :
forall x y z : set, x :e (UPair y z) -> x = y \/ x = z.

(** Given a set X, (Union X) is the set {x | there is some Y such that x :e Y and Y :e X}. That is, Union gives the union of a set of sets. **)

Parameter Union : set -> set.

Axiom UnionI :
forall X x Y : set, x :e Y -> Y :e X -> x :e (Union X).

Axiom UnionE :
forall X x : set, x :e (Union X) -> exists Y : set, x :e Y /\ Y :e X.

(** Given a set X and a function F, (Repl F X) is the set {F x|x :e X}. That is, Repl allows us to form a set by
 replacing the elements x in a set X with corresponding elements F x. **)

Parameter Repl : (set -> set) -> set -> set.

Axiom ReplI :
forall X : set, forall F : set -> set, forall x : set, x :e X -> (F x) :e (Repl F X).

Axiom ReplE :
forall X : set, forall F : set -> set, forall y : set, y :e (Repl F X) -> exists x : set, x :e X /\ y = F x.

(** (Power X) is the set of all subsets of X. **)

Parameter Power : set -> set.

Axiom PowerI : forall X Y : set, Y c= X -> Y :e (Power X).

Axiom PowerE : forall X Y : set, Y :e (Power X) -> Y c= X.

(** Every set is a member of a Grothendieck universe. A Grothendieck universe is a transitive set closed under the previous
set theoretic operators. The assumption that Grothendieck universes exist is stronger than an axiom of infinity since (GU Empty) is infinite.
We also assume (GU X) is the least Grothendieck universe containing X. **)

Parameter GU : set -> set.

Axiom GUIn : forall N : set, N :e (GU N).

Axiom GUTrans : forall N X Y : set, X :e (GU N) -> Y :e X -> Y :e (GU N).

Axiom GUUPair : forall N X Y : set, X :e (GU N) -> Y :e (GU N) -> (UPair X Y) :e (GU N).

Axiom GUPower : forall N X : set, X :e (GU N) -> (Power X) :e (GU N).

Axiom GUUnion : forall N X : set, X :e (GU N) -> (Union X) :e (GU N).

Axiom GURepl : forall N X : set, forall F : set -> set, X :e (GU N) -> (forall x : set, x :e X -> (F x) :e (GU N)) -> (Repl F X) :e (GU N).

Axiom GUMin : forall N U : set, N :e U
  -> (forall X Y : set, X :e U -> Y :e X -> Y :e U)
  -> (forall X Y : set, X :e U -> Y :e U -> (UPair X Y) :e U)
  -> (forall X : set, X :e U -> (Power X) :e U)
  -> (forall X : set, X :e U -> (Union X) :e U)
  -> (forall X : set, forall F:set -> set, X :e U -> (forall x:set, x :e X -> (F x) :e U) -> (Repl F X) :e U)
  -> (GU N) c= U.

End TG.