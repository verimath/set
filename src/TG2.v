(*** Jonas Kaiser, July 2012 ***)
(*** This file develops a set theory, based on the
     Axiomatisation defined in TG0.v and its
     Top-Level unfolding in TG1.v
 ***)

Set Implicit Arguments.

Require Export TG1.

(* ----------------------------------------------------------- *)
Definition inh_set := fun S: set => exists w, w :e S.

(* ----------------------------------------------------------- *)
Lemma Subq_refl : forall A, A c= A.
Proof. intros A a M. exact M. Qed.

Lemma Empty_subq : forall A: set, Empty c= A.
Proof with eauto with TG_set. intros A e C... Qed.

Hint Immediate Subq_refl Empty_subq : TG_set.

Lemma Subq_Empty : forall A, A c= Empty -> A = Empty.
Proof. intros A H. apply set_ext; now eauto with TG_set. Qed.

(* ----------------------------------------------------------- *)
Lemma set_ext_inv : forall A B, A = B -> A c= B /\ B c= A.
Proof with auto with TG_set. intros A B H. split; subst... Qed.

(* ----------------------------------------------------------- *)
Lemma Empty_ni: ~ inh_set Empty.
Proof. intros [e C]. now auto with TG_set. Qed.

Hint Extern 0 =>
  match goal with
  | [ H : inh_set Empty |- _ ] => now destruct (Empty_ni H)
  end : TG_set.

Lemma not_Empty__inh : forall A, A <> Empty <-> inh_set A.
Proof. intros A. split; intros H.
  destruct (classic (inh_set A)) as [H'|H']; [exact H'|].
    exfalso. apply H. apply Subq_Empty; intros a M.
      exfalso. apply H'. exists a. exact M.
  intros E. now auto with TG_set. 
Qed.

Lemma Empty__not_inh : forall A, A = Empty <-> ~ inh_set A.
Proof. intros A. split; intros H. 
  now auto with TG_set.
  apply Subq_Empty; intros a M. exfalso. apply H. now exists a.
Qed.

Lemma Empty_or_inh : forall A, A = Empty \/ inh_set A.
Proof. intros A. destruct (classic (A = Empty)) as [E|H].
    now auto.
    apply not_Empty__inh in H. now auto.
Qed.

Lemma Mem_Empty__Contra : forall a A, a :e A -> A = Empty -> False.
Proof with auto with TG_set. intros a A C E... Qed.

(* ----------------------------------------------------------- *)
Lemma Sing_char: forall x X, (forall y, y :e X -> y = x) -> x :e X -> X = Sing x.
Proof with auto with TG_set. intros x X H Mx. apply set_ext; intros y My.
  apply H in My. subst...
  apply SingE in My. subst...
Qed.

Lemma Subq_Sing : forall x X, X c= Sing x -> X = Empty \/ X = Sing x.
Proof with eauto with TG_set. intros x X H. destruct (Empty_or_inh X) as [E|[e M]]...
  right. apply Sing_char.
    intros y M'. apply H in M'...
    pose proof (H _ M) as H'. apply SingE in H'. subst...
Qed.

(* ----------------------------------------------------------- *)
Lemma One_i : inh_set One.
Proof with auto with TG_set. exists Empty... Qed.

Hint Immediate One_i : TG_set.

Lemma Empty_One__Contra : Empty <> One.
Proof. intros E. eapply Mem_Empty__Contra. now eapply OneI1. congruence. Qed.

Lemma One_Empty__Contra : One <> Empty.
Proof. intros E. apply Empty_One__Contra. congruence. Qed.

Lemma One_char : forall A, (forall a, a :e A -> a = Empty) -> Empty :e A -> A = One.
Proof. apply Sing_char. Qed.

Lemma Subq_One : forall A, A c= One -> A = Empty \/ A = One.
Proof. now apply Subq_Sing. Qed.

Hint Extern 0 =>
  match goal with
  | [ H: Empty = One |- _ ] => now destruct (Empty_One__Contra H)
  | [ H: One = Empty |- _ ] => now destruct (One_Empty__Contra H)
  end : TG_set.

Lemma Two_i : inh_set Two.
Proof. exists Empty. exact TwoI1. Qed.

Hint Immediate Two_i : TG_set.

Lemma Empty_MM_Two : forall E O, E :e O -> O :e Two -> E = Empty. 
Proof. intros E O M1 M2. apply TwoE in M2. destruct M2 as [H|H]; now auto with TG_set. Qed.  

Lemma Two_i__One : forall S, S :e Two -> inh_set S -> S = One.
Proof. intros S S_T I. destruct (TwoE S_T); now eauto with TG_set. Qed.

Hint Extern 0 =>
  match goal with
  | [ M1 : In ?E ?O, M2 : In ?O Two |- _ ] => pose proof (Empty_MM_Two M1 M2)
  end : TG_set.

(* ----------------------------------------------------------- *)
Lemma Repl_Empty : forall F, Repl F Empty = Empty.
Proof. intros F. apply Subq_Empty; intros x H.
  destruct (ReplE H) as [e [C _]]. now auto with TG_set.
Qed.

Hint Rewrite Repl_Empty : TG_set.

Lemma Repl_Empty_inv : forall F X, Repl F X = Empty -> X = Empty.
Proof. intros F X H. apply Subq_Empty; intros x K.
  exfalso. now apply (Mem_Empty__Contra (ReplI F K) H).
Qed.

(* ----------------------------------------------------------- *)
Lemma Union_Empty : Union Empty = Empty.
Proof. apply Subq_Empty; intros x H.
  destruct (UnionE H) as [X [_ C]]; now auto with TG_set.
Qed.

Lemma Union_Sing : forall X, Union (Sing X) = X.
Proof with subst; eauto with TG_set. intros X. apply set_ext; intros x M...
  destruct (UnionE M) as [Y [A B]]. apply SingE in B...
Qed.

Lemma Union_One : Union One = Empty.
Proof. now apply Union_Sing. Qed.

Lemma Union_Two : Union Two = One.
Proof with eauto with TG_set. apply One_char...
  intros E M. apply UnionE in M. destruct M as [X [A B]]...
Qed.

Hint Rewrite Union_Empty Union_Sing Union_One Union_Two : TG_set.

Lemma Union_Two_Empty : forall Y: set, Y :e Two -> Union Y = Empty.
Proof. intros Y M2. apply Subq_Empty; intros e H.
  apply UnionE in H. destruct H as [E [C M1]]. now auto with TG_set.
Qed.

(* ----------------------------------------------------------- *)
Definition BinUnion : set -> set -> set := fun A => fun B =>
  Union (UPair A B).

Lemma BinUnionI1 : forall A B a: set, a :e A ->
  a :e BinUnion A B. 
Proof. intros A B a H. unfold BinUnion.
  now eauto with TG_set.
Qed.

Lemma BinUnionI2 : forall A B b: set, b :e B ->
  b :e BinUnion A B.
Proof. intros A B a H. unfold BinUnion.
  now eauto with TG_set.
Qed.

Hint Resolve BinUnionI1 BinUnionI2 : TG_set.

Lemma BinUnionE : forall A B x, x :e BinUnion A B ->
  x :e A \/ x :e B.
Proof. intros A B x H. unfold BinUnion in H.
  apply UnionE in H. destruct H as [C [x_T H]].
  apply UPairE in H. destruct H; subst; now auto.
Qed.

Lemma GUBinUnion : forall N X Y, X :e GU N -> Y :e GU N ->
  BinUnion X Y :e GU N.
Proof. intros N X Y MX MY. unfold BinUnion. now auto with TG_set. Qed.

Hint Resolve GUBinUnion : TG_set.

(* ----------------------------------------------------------- *)
Lemma Power_Empty : Power Empty = One.
Proof. apply One_char.
  intros E M. apply PowerE in M. exact (Subq_Empty M).
  now auto with TG_set.
Qed.

Hint Rewrite Power_Empty : TG_set.

Lemma Empty_in_Power : forall A, Empty :e Power A.
Proof. intros A. now auto with TG_set. Qed.

Hint Immediate Empty_in_Power : TG_set.

Lemma Power_One : Power One = Two.
Proof with eauto with TG_set. apply set_ext; intros X MX. 
  apply PowerE in MX. apply Subq_One in MX...
  destruct (TwoE MX)...
Qed.

Hint Rewrite Power_One : TG_set.

(* ----------------------------------------------------------- *)
Definition FamUnion : set -> (set -> set) -> set := fun X F =>
  Union (Repl F X).

Lemma FamUnionI : forall X F x y,
  x :e X -> y :e (F x) -> y :e (FamUnion X F).
Proof. intros X F x y A B. unfold FamUnion. eauto with TG_set. Qed.

Hint Resolve FamUnionI : TG_set.

Lemma FamUnionE : forall X F y,
  y :e (FamUnion X F) -> exists x, x :e X /\ y :e (F x).
Proof. intros X F y A.
  destruct (UnionE A) as [Y [M1 B]]; clear A.
  destruct (ReplE B) as [x [M2 E]]; clear B; subst.
  exists x. now auto.
Qed.

Lemma GUFamUnion : forall N X F, X :e (GU N) ->
  (forall x:set, x :e X -> (F x) :e (GU N)) ->
  FamUnion X F :e GU N.
Proof. intros N X F MX h. unfold FamUnion. auto with TG_set. Qed.

Hint Resolve GUFamUnion : TG_set.

Lemma FamUnion_Empty : forall F, FamUnion Empty F = Empty.
Proof. intros F. unfold FamUnion.
  autorewrite with TG_set. reflexivity.
Qed.

Hint Rewrite FamUnion_Empty : TG_set.

Lemma FamUnion_One : forall X F,
  (forall x, x :e X -> F x :e Two) ->
  (exists x, x :e X /\ F x = One) ->
  FamUnion X F = One.
Proof. intros X F A E. apply One_char.
  intros e H. destruct (FamUnionE H) as [x [Mx Me]]; clear H. apply A in Mx.
    exact (Empty_MM_Two Me Mx).
  destruct E as [x [Mx H']]. apply FamUnionI with (x:=x); eauto with TG_set.
Qed.

Lemma FamUnion_const : forall X F C,
  inh_set X -> (forall x, x :e X -> F x = C) -> FamUnion X F = C.
Proof. intros X F C I H. apply set_ext; intros c M.
  destruct (FamUnionE M) as [x [M' H']]; clear M.
    apply H in M'. congruence. 
  destruct I as [x M'].
    pose proof (H x M') as E. subst. now eauto with TG_set.
Qed.

Lemma FamUnion_const_Empty : forall X F, 
  (forall x: set, x :e X -> F x = Empty) -> FamUnion X F = Empty.
Proof. intros X F H. destruct (Empty_or_inh X) as [E|I]; subst.
  now apply FamUnion_Empty.
  now apply FamUnion_const.
Qed.

Lemma FamUnion_Two : forall X F, 
  (forall x, x :e X -> F x :e Two) -> FamUnion X F :e Two.
Proof with firstorder with TG_set. intros X F H.
  destruct (classic (exists x, x :e X /\ F x = One)) as [A|A].
    rewrite (FamUnion_One _ H A)...
    assert (A': forall x: set, x :e X -> F x = Empty).
      intros x Mx. destruct (TwoE (H x Mx)) as [H'|H']...
    rewrite (FamUnion_const_Empty _ A')...
Qed.

(* ----------------------------------------------------------- *)
Definition Sep : set -> (set -> Prop) -> set := fun X P =>
  epsilon (inhabits Empty) (fun Z => forall x, x :e Z <-> x :e X /\ P x).

Lemma Sep_correct : forall X P x, x :e (Sep X P) <-> x :e X /\ P x.
Proof. intros X P. unfold Sep. apply epsilon_spec.
  destruct (classic (exists x : set, x :e X /\ P x)).
    (* x_def exists *) destruct H as [x_def [M p]].
      set (F_spec x y := P x /\ x = y \/ ~ P x /\ x_def = y).
      set (F x := epsilon (inhabits Empty) (F_spec x)).
      assert (FC: forall x, F_spec x (F x)).
        intros x. refine (epsilon_spec (inhabits Empty) (F_spec x) _). unfold F_spec.
        destruct (classic (P x)) as [p' | p']; [exists x | exists x_def]; tauto.
      assert (A: forall x, P x -> x = F x ) by firstorder.
      assert (B: forall x, ~ P x -> x_def = F x) by firstorder.
      exists (Repl F X). intros x. split; intros H.
        apply ReplE in H. destruct H as [z [K L]].
          destruct (classic (P z)) as [p' | p'].
            assert (E: z = F z) by apply (A _ p'). split; congruence.
            assert (E: x_def = F z) by apply (B _ p'). split; congruence.
        destruct H as [M' p']. assert (E: x = F x) by apply (A _ p').
          rewrite E. auto with TG_set.
    (* no x_def *) exists Empty. firstorder using EmptyE.
Qed.

Lemma SepI : forall X, forall P: set -> Prop, forall x,
  x :e X -> P x -> x :e (Sep X P).
Proof. now firstorder using Sep_correct. Qed.

Hint Resolve SepI : TG_set.

Lemma SepE1 : forall X P x, x :e (Sep X P) -> x :e X.
Proof. now firstorder using Sep_correct. Qed.

Lemma SepE2 : forall X P x, x :e (Sep X P) -> P x.
Proof. now firstorder using Sep_correct. Qed.

Lemma SepE : forall X P x, x :e (Sep X P) -> x :e X /\ P x.
Proof. now firstorder using Sep_correct. Qed.

Lemma Sep_smaller : forall X P, Sep X P c= X.
Proof. unfold Subq. exact SepE1. Qed.

Hint Immediate Sep_smaller : TG_set.

Lemma Sep_Empty : forall P, Sep Empty P = Empty.
Proof. intros P. apply Subq_Empty. now eauto with TG_set. Qed.

Hint Rewrite Sep_Empty : TG_set.

Lemma Sep_Empty_inv : forall X P,
  Sep X P = Empty -> forall x, x :e X -> ~ P x.
Proof with auto with TG_set. intros X P E x x_T H.
  cut (x :e Empty)... rewrite <- E. apply SepI...
Qed.

Lemma Sep_One : forall P, Sep One P = One \/ Sep One P = Empty.
Proof. intros P. pose proof (Sep_smaller One P) as H. apply Subq_One in H; tauto. Qed.

Lemma Sep_Sing : forall x P,
  (Sep (Sing x) P = (Sing x) /\ P x) \/ (Sep (Sing x) P = Empty /\ ~ P x). 
Proof with auto with TG_set. intros x P.
  pose proof (Sep_smaller (Sing x) P) as H. apply Subq_Sing in H; destruct H.
  right. split... apply Sep_Empty_inv with (X:=(Sing x))...
  left. split... apply SepE2 with (X := Sing x). rewrite H...
Qed.

Lemma Sep_Power : forall X P, Sep X P :e Power X. 
Proof. intros X P. eauto with TG_set. Qed.

Hint Immediate Sep_Power : TG_set.

Lemma GUSep : forall N X P, X :e GU N -> Sep X P :e GU N.
Proof. intros N X P MX. apply GUTrans with (X:= Power X);
  now auto with TG_set.
Qed.

Hint Resolve GUSep : TG_set.

(* ----------------------------------------------------------- *)
Definition Inter : set -> set := fun M =>
  Sep (Union M) (fun x : set => forall A : set, A :e M -> x :e A).

Lemma Inter_Empty : Inter Empty = Empty. 
Proof. unfold Inter. autorewrite with TG_set. reflexivity. Qed.

Hint Rewrite Inter_Empty : TG_set.

Lemma InterI : forall x M, inh_set M ->
  (forall A, A :e M -> x :e A) -> x :e Inter M.
Proof. intros x M I H. unfold Inter. refine (SepI _ _ H).
  destruct I as [A K]. eauto with TG_set.
Qed.

Hint Resolve InterI : TG_set.

Lemma InterE : forall x M,
  x :e Inter M -> inh_set M /\ forall A, A :e M -> x :e A.
Proof. intros x M H. split.
  apply SepE1 in H. apply UnionE in H. destruct H as [Y [_ H]]. now exists Y.
  now apply (SepE2 _ _ H).
Qed.

Lemma GUInter : forall N X, X :e GU N -> Inter X :e GU N.
Proof. intros N X MX. unfold Inter. now auto with TG_set. Qed.

Hint Resolve GUInter : TG_set.

Lemma Inter_correct : forall x M,
  (x :e Inter M  <-> inh_set M /\ forall A, A :e M -> x :e A).
Proof. intros x M. split; intros H.
  now firstorder using InterE.
  now firstorder using InterI.
Qed.

(* ----------------------------------------------------------- *)
Lemma GU_is_universe : forall N, grothendieck_universe (GU N).
Proof. intros N.
  split. unfold transitive_set; apply GUTrans.
  now firstorder with TG_set.
Qed.

Lemma uc_upair : forall U X Y: set, grothendieck_universe U ->
  X :e U -> Y :e U -> (UPair X Y) :e U. 
Proof. now firstorder with TG_set. Qed.

Hint Resolve uc_upair : TG_set.

Lemma uc_power : forall U X: set, grothendieck_universe U ->
  X :e U -> (Power X) :e U. 
Proof. now firstorder with TG_set. Qed.

Hint Resolve uc_power : TG_set.

Lemma uc_union : forall U X: set, grothendieck_universe U ->
  X :e U -> (Union X) :e U. 
Proof. now firstorder with TG_set. Qed.

Hint Resolve uc_union : TG_set.

Lemma uc_repl : forall U X: set, forall F: set -> set, grothendieck_universe U ->
  X :e U -> (forall x, x :e X -> F x :e U) -> (Repl F X) :e U. 
Proof. now firstorder with TG_set. Qed.

Hint Resolve uc_repl : TG_set.

Lemma uc_sing : forall U x: set, grothendieck_universe U ->
  x :e U -> (Sing x) :e U. 
Proof. intros. now eauto with TG_set. Qed.

Hint Resolve uc_sing : TG_set.

Lemma uc_famunion : forall U I: set, forall F: set -> set, grothendieck_universe U ->
  I :e U -> (forall i, i :e I -> F i :e U) -> (FamUnion I F) :e U. 
Proof. intros. now eauto with TG_set. Qed.

Hint Resolve uc_famunion : TG_set.

Lemma uc_sep : forall U X: set, forall P: set -> Prop, grothendieck_universe U ->
  X :e U -> (Sep X P) :e U. 
Proof. now firstorder with TG_set. Qed.

Hint Resolve uc_sep : TG_set.

Lemma uc_inter : forall U X: set, grothendieck_universe U ->
  X :e U -> (Inter X) :e U. 
Proof. intros U X G MX. unfold Inter. now eauto with TG_set. Qed.

Hint Resolve uc_inter : TG_set.

Lemma uc_binunion : forall U X Y, grothendieck_universe U ->
  X :e U -> Y :e U -> (BinUnion X Y) :e U.
Proof. now firstorder with TG_set. Qed.

Hint Resolve uc_binunion : TG_set.