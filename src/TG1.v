(*** Jonas Kaiser, February 2012 ***)
(*** This file unfolds the TG Axiomatisation in TG0.v
     to Top-Level
 ***)

Set Implicit Arguments.

Require Export TG0.

Declare Module M : TG.
Export M.

(*** Improve Automation for set-theoretic reasoning in TG ***)

Create HintDb TG_set.

(* Creat useful hints for stuff in TG0 *)

Hint Extern 0 =>
  match goal with
  | [ H : In ?A Empty |- _ ] => now destruct (EmptyE H)
  end : TG_set.

Hint Extern 0 =>
  match goal with
  | [ H : ?A = Empty |- _ ] => rewrite H in *
  | [ H : Empty = ?A |- _ ] => rewrite <- H in *
  end : TG_set.

Hint Resolve UPairI1 UPairI2 UnionI ReplI PowerI GUIn GUUPair GUPower GUUnion GURepl : TG_set.

(*** Extensions of the set theory required for Specs.v ***)

(* Singleton sets *)
Definition Sing : set -> set := fun X:set => UPair X X.

Lemma SingI : forall X, X :e (Sing X). 
Proof. intros X. exact (UPairI1 X X). Qed.

Lemma SingE : forall X Y, Y :e (Sing X) -> Y = X.
Proof. intros X Y A. destruct (UPairE A) as [B|B]; assumption. Qed.

Lemma GUSing : forall N X, X :e GU N -> Sing X :e GU N.
Proof. intros N X MX. unfold Sing. now auto with TG_set. Qed.

Hint Immediate SingI SingE : TG_set.
Hint Resolve GUSing : TG_set.

(* The set 1 *)
Definition One : set := Sing Empty.

Lemma OneI1 : Empty :e One.
Proof. now apply SingI. Qed.

Lemma OneI2 : forall A, A = Empty -> A :e One.
Proof. intros. subst. exact OneI1. Qed.

Lemma OneE: forall A, A :e One -> A = Empty.
Proof. now apply SingE. Qed.

Hint Immediate OneI1 : TG_set.
Hint Extern 0 =>
  match goal with
  | [ H : ?A = One |- _ ] => rewrite H in *
  | [ H : One = ?A |- _ ] => rewrite <- H in *
  end : TG_set.

(* The set 2 *)
Definition Two : set := UPair Empty One.

Lemma TwoI1 : Empty :e Two.
Proof. now apply UPairI1. Qed.

Lemma TwoI2 : One :e Two.
Proof. now apply UPairI2. Qed.

Lemma TwoI3 : forall A, A = Empty \/ A = One -> A :e Two.
Proof. intros A [E|E]; subst; [now apply TwoI1 | now apply TwoI2]. Qed.

Lemma TwoE : forall A, A :e Two -> A = Empty \/ A = One.
Proof. intros. apply UPairE. exact H. Qed.

Hint Immediate TwoI1 TwoI2 : TG_set.
Hint Resolve TwoI3 : TG_set.
Hint Extern 0 =>
  match goal with
  | [ H : ?A = Two |- _ ] => rewrite H in *
  | [ H : Two = ?A |- _ ] => rewrite <- H in *
  end : TG_set.

(* Notion of a transitive set *)
Definition transitive_set : set -> Prop := fun S: set =>
  forall X x: set, X :e S -> x :e X -> x :e S.

(* When is a set a proper Grothendieck Universe *) 
Definition grothendieck_universe : set -> Prop := fun U: set =>
     transitive_set U
  /\ (forall X Y: set, X :e U -> Y :e U -> (UPair X Y) :e U)
  /\ (forall X: set, X :e U -> (Power X) :e U)
  /\ (forall X: set, X :e U -> (Union X) :e U)
  /\ (forall X: set, forall F: set -> set, X :e U ->
      (forall x: set, x :e X -> F x :e U) -> (Repl F X) :e U).