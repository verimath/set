(*** Jonas Kaiser, July 2012 ***)
(*** This file extends the set theory with
     - Kuratowski Pairs
     - Aczel Functions
 ***)

Set Implicit Arguments.

Require Export TG2.

(* We need to be able to extract information from
   equalities of unordered pairs and or singltons *)
Lemma UU_ex : forall W X Y Z, UPair W X = UPair Y Z ->
  ( W = Y /\ X = Z ) \/ ( W = Z /\ X = Y ).
Proof with auto with TG_set. intros W X Y Z H. 
  assert (C: W :e UPair Y Z). rewrite <- H...
  assert (D: X :e UPair Y Z). rewrite <- H...
  assert (E: Y :e UPair W X). rewrite H...
  assert (F: Z :e UPair W X). rewrite H...
  clear H.
  apply UPairE in C. apply UPairE in D.
  apply UPairE in E. apply UPairE in F.
  destruct C, D, E, F; now firstorder.
Qed.

Lemma SU_ex : forall X Y Z, Sing X = UPair Y Z -> X = Y /\ X = Z.
Proof. intros X Y Z H. apply UU_ex in H. now firstorder. Qed.

Lemma US_ex : forall X Y Z, UPair Y Z = Sing X -> X = Y /\ X = Z.
Proof. intros X Y Z H. apply eq_sym in H. exact (SU_ex H). Qed. 

Lemma SS_ex : forall X Y, Sing X = Sing Y -> X = Y.
Proof. intros X Y H. apply SU_ex in H. now firstorder. Qed.

Ltac inv_SU_eq :=
  repeat let E1 := fresh "E" in
         let E2 := fresh "E" in
         let E3 := fresh "E" in
         let E4 := fresh "E" in
         match goal with
         | [H : UPair ?A ?B = UPair ?C ?D |- _ ] =>
             destruct (UU_ex H) as [[E1 E2] | [E3 E4]]; clear H; subst
         | [H : Sing ?A = UPair ?B ?C |- _ ] =>
             destruct (SU_ex H) as [E1 E2]; clear H; subst
         | [H : UPair ?A ?B = Sing ?C |- _ ] =>
             destruct (US_ex H) as [E1 E2]; clear H; subst
         | [H : Sing ?A = Sing ?B |- _ ] =>
             apply SS_ex in H; subst
         end.

(* Ordered Pairs a la Kuratowski *)
Definition op_k : set -> set -> set := fun x y: set =>
  UPair (Sing x) (UPair x y).
Notation "( x , y )k" := (op_k x y). (* level annotation? *)

(* uses (necessary?): <none> *)
(* Lemma op_k_same : forall x y, x = y -> (x,y)k = Sing (Sing x).
Proof. intros x y E. now rewrite E. Qed.*)

(* uses (necessary?): <none> *)
(* Lemma op_k_I1 : forall x y Y, Y :e (x,y)k -> x :e Y.
Proof. intros x y Y H. apply UPairE in H.
  destruct H; subst; eauto with TG_set.
Qed. *)

(* uses (necessary?): <none> *)
(* Lemma op_k_I2 : forall x y,
  (exists Y: set, Y :e (x,y)k /\ y :e Y ) /\
  (forall Y1 Y2: set, Y1 :e (x,y)k -> Y2 :e (x,y)k ->
   ~(Y1 = Y2) -> (y /:e Y1 \/ y /:e Y2)).
Proof. intros x y. split.
  exists (UPair x y). split; apply UPairI2.
  intros Y1 Y2 H1 H2 C. apply UPairE in H1. apply UPairE in H2.
    destruct H1, H2; try congruence; subst; [left | right];
    intros M; apply SingE in M; subst; apply C; reflexivity.
Qed. *)

Lemma op_k_union : forall x y, Union (x,y)k = UPair x y.
Proof with subst; eauto with TG_set. intros x y. apply set_ext; intros n H. 
  destruct (UnionE H) as [Y [A B]]. destruct (UPairE B)...
    apply SingE in A...
  destruct (UPairE H)...
Qed.

Hint Rewrite op_k_union : TG_set.

Lemma op_k_inter : forall x y, Inter (x,y)k = Sing x.
Proof with subst; eauto with TG_set. intros x y. apply set_ext; intros n H.
  apply SepE2 in H. apply H...
  apply SingE in H. apply SepI...
    intros Y H. apply UPairE in H.
    destruct H; subst; eauto with TG_set.
Qed.

Hint Rewrite op_k_inter : TG_set.

(* left projection *)
Definition proj1_op_k : set -> set := fun p => Union (Inter p).

Lemma proj1_op_k_correct : forall x y, proj1_op_k (x,y)k = x.
Proof. intros x y. unfold proj1_op_k.
  now autorewrite with TG_set.
Qed.

Hint Rewrite proj1_op_k_correct : TG_set.

Definition proj2_op_k : set -> set := fun p => Union (Sep (Union p)
  (fun x : set => x :e Inter p -> Union p = Inter p)).

Lemma proj2_op_k_correct : forall x y, proj2_op_k (x,y)k = y.
Proof with subst; eauto with TG_set. intros x y. unfold proj2_op_k.
  autorewrite with TG_set.
  apply set_ext; intros n H.
    destruct (UnionE H) as [y' [H' K]]; clear H.
      apply SepE in K. destruct K as [K H]; destruct (UPairE K)...
        specialize (H (SingI x)).
        apply US_ex in H; destruct H...
    apply UnionI with (Y := y)...
      apply SepI...
      intros H'. apply SingE in H'...
Qed.

Hint Rewrite proj2_op_k_correct : TG_set.

(* Old versions or right projection, here the condition is stated
   in negative form and hance we need classic to remove a double
   negation, tha above version is cleaner, but they are equivalent *)
Definition proj2'_op_k : set -> set := fun p => Union (Sep (Union p)
  (fun x : set => Union p <> Inter p -> x /:e Inter p)).

Lemma proj2'_op_k_correct : forall x y, proj2'_op_k (x,y)k = y.
Proof with subst; eauto with TG_set. intros x y. unfold proj2'_op_k.
  autorewrite with TG_set.
  apply set_ext; intros n H.
    destruct (UnionE H) as [y' [H' K]].
      assert (K': y' :e UPair x y). apply (SepE1 _ _ K).
        destruct (UPairE K') as [E|E]...
          apply SepE2 in K.
          destruct (classic (y = x)) as [E|E]...
            exfalso. apply K...
              intros E'. destruct (US_ex E')...
    apply UnionI with (Y := y)...
      apply SepI...
      intros H' C. apply SingE in C...
Qed.

Lemma op_k_correct : forall a b c d,
  (a,b)k = (c,d)k <-> a = c /\ b = d.
Proof. intros a b c d. split; intros H.
  split.
    pose proof (proj1_op_k_correct a b) as K.
      rewrite H in K. rewrite proj1_op_k_correct in K. congruence.
    pose proof (proj2_op_k_correct a b) as K.
      rewrite H in K. rewrite proj2_op_k_correct in K. congruence.
  destruct H as [A B]. congruence.
Qed.

(* Characterising Pairs, without projections, s.b. for alternative *)
Definition is_pair : set -> Prop := fun p => exists x, exists y, p = (x,y)k.

Lemma op_k_eta : forall p, is_pair p <-> p = (proj1_op_k p, proj2_op_k p)k.
Proof. intros p. split; intros H.
  destruct H as [a [b E]]. rewrite E. now autorewrite with TG_set.
  now exists (proj1_op_k p), (proj2_op_k p).
Qed.

(* Cartesian Products *)
Definition CProd:set -> set -> set := fun A B =>
  FamUnion A (fun a => Repl (fun b => (a,b)k ) B).

Lemma CProdI : forall a A b B, a :e A -> b :e B -> (a,b)k :e CProd A B.
Proof. intros a A b B M1 M2. unfold CProd. now eauto with TG_set. Qed.

Hint Resolve CProdI : TG_set.

Lemma CProdE1 : forall p A B, p :e CProd A B -> proj1_op_k p :e A /\ proj2_op_k p :e B.
Proof. intros p A B M. 
  destruct (FamUnionE M) as [a [M1 H1]]; clear M.
  destruct (ReplE H1) as [b [M2 E]]; clear H1; subst.
  autorewrite with TG_set. now auto.
Qed.

Lemma CProdE2 : forall p A B, p :e CProd A B -> is_pair p.
Proof. intros p A B H. 
  destruct (FamUnionE H) as [a [M1 H1]]; clear H.
  destruct (ReplE H1) as [b [M2 E]]; clear H1; subst.
  now exists a, b.
Qed.

Lemma CProd_correct : forall p A B,
  p :e CProd A B <-> exists a, exists b, p = (a,b)k /\ a :e A /\ b :e B.
Proof. intros p A B. split; intros H.
  (* -> *) 
    destruct (CProdE1 H) as [E1 E2].
    destruct (CProdE2 H) as [a [b H']].
    exists a, b. subst p. autorewrite with TG_set in E1, E2. now auto.
  (* <- *)
    destruct H as [a [b [E [M1 M2]]]]. subst. eauto with TG_set.
Qed.

Lemma CProd_Empty1 : forall B, CProd Empty B = Empty.
Proof. intros B. unfold CProd. now autorewrite with TG_set. Qed.
 
Lemma CProd_Empty2 : forall A, CProd A Empty = Empty.
Proof. intros B. apply Subq_Empty; intros p H.
  destruct (CProdE1 H). eauto with TG_set.
Qed.

Hint Rewrite CProd_Empty1 CProd_Empty2 : TG_set.

(* Aczel Functions *)
(* ap f x := {y | (x,y) :e f}
   lam X F := {(x,y) | x :e X /\ y :e F x}
   Pi X Y := {lam X F | forall x, x :e X -> F x :e Y x}
           = { f :e Pow (X * U(FU(X Y))) | forall x, x :e X -> ap f x :e Y x }
           = { f :e Pow (sig x:X U(Y x)) | forall x, x :e X -> ap f x :e Y x }
*)

Definition ap_a : set -> set -> set := fun f x =>
    Repl proj2_op_k (Sep f (fun p => proj1_op_k p = x /\ is_pair p)).
Definition lam_a : set -> (set -> set) -> set := fun X F =>
    FamUnion X (fun x => Repl (fun y => (x,y)k ) (F x)).

Lemma lam_a__CProd : forall A B : set, CProd A B = lam_a A (fun _ => B).
Proof. reflexivity. Qed.

Definition Pi_a : set -> (set -> set) -> set := fun X Y => 
    Sep (Power (CProd X (Union (FamUnion X Y))))
        (fun f => forall x, x :e X -> ap_a f x :e Y x).

(* Several Lemmas implementing the typing rules of CC *)
Lemma lam_a_ext : forall X: set, forall f1 f2: set -> set,
    (forall y, y :e X -> f1 y = f2 y) ->
    lam_a X f1 = lam_a X f2.
Proof with eauto with TG_set. intros X f1 f2 FE. unfold lam_a. apply set_ext; intros s H;
  destruct (FamUnionE H) as [x [M H1]]; clear H; subst.
  rewrite (FE x M) in H1...
  rewrite <- (FE x M) in H1...
Qed.

Lemma Pi_a_ext : forall X: set, forall Y1 Y2: set -> set,
  (forall y, y :e X -> Y1 y = Y2 y) -> Pi_a X Y1 = Pi_a X Y2.
Proof with eauto with TG_set. intros X Y1 Y2 FE. unfold Pi_a.
  apply set_ext; intros f H; apply Sep_correct in H;
  destruct H as [H E]; apply PowerE in H; apply SepI.
  (* -> *)
    apply PowerI. intros p M. apply H in M; clear H. apply CProd_correct in M.
      destruct M as [a [b [E1 [M1 H']]]]; subst.
      destruct (UnionE H') as [B [M2 H'']]; clear H'.
      destruct (FamUnionE H'') as [x [M3 H']]; clear H''.
      rewrite (FE x M3) in H'...
    intros x M. rewrite <- (FE x M)...
  (* <- *)
    apply PowerI. intros p M. apply H in M; clear H. apply CProd_correct in M.
      destruct M as [a [b [E1 [M1 H']]]]; subst.
      destruct (UnionE H') as [B [M2 H'']]; clear H'.
      destruct (FamUnionE H'') as [x [M3 H']]; clear H''.
      rewrite <- (FE x M3) in H'...
    intros x M. rewrite (FE x M)...
Qed.

Lemma beta_a : forall X: set, forall F: set -> set,
  forall x: set, x :e X -> ap_a (lam_a X F) x = F x.
Proof. intros X F x H. apply set_ext; intros y M.
  (* -> *)
    destruct (ReplE M) as [p [H' E]]; clear M; subst.
    apply Sep_correct in H'. destruct H' as [H' [E _]]; subst.
    destruct (FamUnionE H') as [x [_ A]]; clear H'.
    destruct (ReplE A) as [y [M2 E]]; clear A; subst.
    now autorewrite with TG_set.
  (* <- *)
    rewrite <- (proj2_op_k_correct x y). apply ReplI. apply SepI.
    apply FamUnionI with (x:=x); eauto with TG_set.
    split. 
      now apply proj1_op_k_correct.
      now exists x, y.
Qed.

Lemma lam_a_pair : forall p X F, p :e lam_a X F -> exists x, exists y,
  x :e X /\ y :e F x /\ p = (x,y)k.
Proof. intros p X F H. 
  destruct (FamUnionE H) as [x [Mx H']]; clear H.
  destruct (ReplE H') as [y [My E]]; clear H'.
  exists x, y. now auto.
Qed.

Lemma lam_a_Pi_a : forall X: set, forall Y: set -> set,
  forall F: set -> set, (forall x: set, x :e X -> F x :e Y x) ->
  lam_a X F :e Pi_a X Y.
Proof. intros X Y F A. unfold Pi_a.
  apply SepI.
    Focus 2. intros x M. rewrite (beta_a _ M). exact (A x M).
    apply PowerI. intros p H.
      apply lam_a_pair in H.
      destruct H as [x [y [x_T [y_T E]]]]. subst.
        apply CProdI. exact x_T.
        eapply UnionI. eapply y_T.
      now eauto with TG_set.
Qed.

Lemma ap_a_Pi_a : forall X: set, forall Y: set -> set,
  forall f: set, forall x: set,
  f :e Pi_a X Y -> x :e X -> ap_a f x :e Y x.
Proof. intros X Y f x H M1. apply SepE2 in H. now apply H. Qed.

(* This Lemma will implement the impredicativity of Prop, when defined as Two *)
Lemma Pi_a_Two : forall X: set, forall Y: set -> set,
  (forall x, x :e X -> Y x :e Two) -> Pi_a X Y :e Two.
Proof. intros X Y H. unfold Pi_a.
  assert (H': FamUnion X Y :e Two) by apply (FamUnion_Two _ H).
  apply Union_Two_Empty in H'. rewrite H'.
  autorewrite with TG_set. rewrite <- Power_One.
  now eauto with TG_set.
Qed.

(* Additional shorthand for non-dependant Arrow types *)
Definition Arr_a : set -> set -> set := fun A B => Pi_a A (fun _ => B).
  
Lemma ap_a_Arr_a : forall A: set, forall B: set,
  forall f: set, forall a: set,
  f :e (Arr_a A B) -> a :e A -> ap_a f a :e B.
Proof. intros A B f a H1 H2. now apply (ap_a_Pi_a _ H1 H2). Qed.

(* Since we have the implementations of these ap lam and Pi
   available when can exploit the encoding for further Facts *)

(* relates the members of a valid function set to
   what happens when we 'apply' that set *) 
Lemma ap_a_pair : forall x y f, y :e ap_a f x <-> (x,y)k :e f.
Proof. split; intros H.
  destruct (ReplE H) as [p [H' E2]]; clear H.
    pose proof (SepE1 _ _ H') as mem_p.
    apply SepE2 in H'. destruct H' as [E1 H]. apply op_k_eta in H.
    congruence.
  rewrite <- (proj2_op_k_correct x y).
    apply ReplI. apply SepI. exact H.
    split.
      now apply proj1_op_k_correct.
      now exists x, y.
Qed.

Lemma fun_subq : forall A F f g, f :e Pi_a A F ->
  (forall x, x :e A -> ap_a f x c= ap_a g x) -> f c= g.
Proof. intros A F f g f_T H. intros p H'.
  apply SepE1 in f_T. apply PowerE in f_T.
  pose proof (f_T _ H') as J.
  apply CProd_correct in J. destruct J as [x [y [Ep [x_T y_T]]]].
  assert (L1: y :e ap_a f x). apply ap_a_pair. congruence.
  pose proof (H x x_T) as Ea. apply Ea in L1. apply ap_a_pair in L1.
  congruence.
Qed.

Lemma fun_ext : forall A F f g, f :e Pi_a A F -> g :e Pi_a A F ->
  (forall x, x :e A -> ap_a f x = ap_a g x) -> f = g.
Proof. intros A F f g f_T g_T H.
  apply set_ext; eapply fun_subq; try eassumption; intros x x_T;
  apply set_ext_inv; pose proof (H x x_T) as H'; congruence.
Qed.

Lemma fun_eta : forall A B f, f :e Pi_a A B -> f = lam_a A (fun x => ap_a f x).
Proof. intros A B f f_T. eapply fun_ext.
  now eapply f_T.
  apply lam_a_Pi_a. intros a a_T. now apply (ap_a_Pi_a _ f_T a_T).
  intros a a_T. now rewrite beta_a. 
Qed.

(* not sure if I need this .. ? *) 
Lemma lam_a_beta_a : forall X F, lam_a X F = lam_a X (fun x => ap_a (lam_a X F) x).
Proof. intros X F. apply lam_a_ext. intros y D. now rewrite beta_a. Qed.

(* applying a lambda to something outside its domain yields Empty ***)
Lemma beta_a_undef_Empty : forall X x F, x /:e X -> ap_a (lam_a X F) x = Empty.
Proof. intros X x F H. apply Subq_Empty; intros w M.
  apply ap_a_pair in M. apply lam_a_pair in M.
  destruct M as [x' [y' [H' [_ E]]]].
  apply op_k_correct in E. destruct E. congruence.
Qed.

(* applying Empty to anything always yields Empty *)
Lemma ap_a_Empty : forall A, ap_a Empty A = Empty.
Proof. intros A. unfold ap_a. now autorewrite with TG_set. Qed.

Hint Rewrite ap_a_Empty : TG_set.

(* a tactic that collapses beta redeces as far as possible *)
Ltac col_redex_a :=
repeat match goal with
       | [ H: context[ap_a Empty _] |- _ ] => rewrite ap_a_Empty in H
       | |- context[ap_a Empty _] => rewrite ap_a_Empty
       | [ H: context[ap_a (lam_a ?A ?f) ?a], G: In ?a ?A |- _ ] =>
           rewrite (beta_a _ G) in H
       | [ G: In ?a ?A |- context[ap_a (lam_a ?A ?f) ?a]] =>
           rewrite (beta_a _ G)
       | [ H: context[ap_a (lam_a ?A ?f) ?a], G: ~ In ?a ?A |- _ ] =>
           rewrite (beta_a_undef_Empty _ G) in H
       | [ G: ~ In ?a ?A |- context[ap_a (lam_a ?A ?f) ?a]] =>
           rewrite (beta_a_undef_Empty _ G)
       end.

(* Universe Closure Lemmas *)
Lemma uc_opair : forall U x y: set, grothendieck_universe U ->
  x :e U -> y :e U -> (x,y)k :e U. 
Proof. intros U x y G Mx My. unfold op_k. now eauto with TG_set. Qed.

Hint Resolve uc_opair : TG_set.

Lemma uc_cprod : forall U X Y: set, grothendieck_universe U ->
  X :e U -> Y :e U -> (CProd X Y) :e U.
Proof. intros U X Y G MX MY. assert (T: transitive_set U) by apply G. unfold CProd.
  apply (uc_famunion _ G MX). intros x Mx. apply (T _ _ MX) in Mx.
  apply (uc_repl _ G MY). intros y My. apply (T _ _ MY) in My.
  now apply uc_opair.
Qed.

Hint Resolve uc_cprod : TG_set.