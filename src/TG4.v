(*** Jonas Kaiser, July 2012 ***)
(*** This file extends the set theory with
     - naturals
 ***)

Set Implicit Arguments.

Require Export TG3.

(* Here I am using the ordinals to encode nat*)

Definition ordO : set := Empty.
Definition ordS : set -> set := fun N => BinUnion N (Sing N). 
Definition FinOrd : set := Sep (GU Empty)
  (fun N => exists n: nat, iter n ordS ordO = N).

Lemma GUordS : forall X N, X :e GU N -> ordS X :e GU N.
Proof. intros X N H.
  apply GUBinUnion. exact H.
  apply GUSing. exact H.
Qed.

(* These Lemmas represent a notion of typing related to FinOrd *)
Lemma FinOrd_T : FinOrd :e GU (GU Empty).
Proof.
  assert (H: FinOrd c= GU Empty) by apply Sep_smaller.
  apply PowerI in H.
  apply GUTrans with (X:= Power (GU Empty)).
  apply GUPower. now apply GUIn.
  exact H.
Qed.

Hint Immediate FinOrd_T : TG_set.

Lemma ordO_T : ordO :e FinOrd.
Proof. apply SepI.
  now apply GUIn.
  now exists 0.
Qed.

Hint Immediate ordO_T : TG_set.

Lemma ordS_T : forall N, N :e FinOrd -> ordS N :e FinOrd.
Proof. intros N H.
  destruct (SepE _ _ H) as [N_T [n E]]. apply SepI.
    now apply GUordS.
    exists (S n). simpl. congruence.
Qed.

Hint Resolve ordS_T : TG_set.

Lemma iter_ord_T : forall n: nat, iter n ordS ordO :e FinOrd.
Proof. induction n; simpl.
  exact ordO_T.
  now apply ordS_T.
Qed.

(* any set starting with S is inhabited *)
Lemma ordS_i : forall N, inh_set (ordS N).
Proof. intros N. exists N. unfold ordS. auto with TG_set. Qed.

(* hence S and O are disjoint *)
Lemma ordS_neq_ordO : forall N, ordS N <> ordO.
Proof. intros N.
  unfold ordO. apply not_Empty__inh.
  now apply ordS_i.
Qed.

(* well-founded: contradicting one-cycle  *)
Lemma wf_1c : forall A: set, A /:e A. 
Proof. apply In_ind. intros A IH H.
  apply (IH A H H).
Qed.

(* well-founded: contradicting two-cycle  *)
Lemma wf_2c : forall A B: set, A :e B -> B /:e A.
Proof. apply (In_ind (fun A: set => forall B: set, A :e B -> B /:e A)).
  intros A IH B ab ba. apply (IH B ba A); auto.
Qed.

(* the S operation is injective *) 
Lemma ordS_inj : forall N M, ordS N = ordS M -> N = M.
Proof with auto with TG_set. intros N M E. unfold ordS in E.
  assert (HN: N :e BinUnion N (Sing N))...
  rewrite E in HN. apply BinUnionE in HN. destruct HN...
  apply eq_sym.
  assert (HM: M :e BinUnion M (Sing M))...
  rewrite <- E in HM. apply BinUnionE in HM. destruct HM...
  exfalso. now apply (@wf_2c N M).
Qed.

(* Embedding and projection functions for my nats *)
Definition FinOrd_embed (n: nat) : set := iter n ordS ordO.
Definition FinOrd_proj (N: set) : nat :=
  match dit {n: nat | iter n ordS ordO = N} with
    | inl (exist _ n _) => n
    | inr _ => 0
  end.
(* REMARK: projection is total, i.e. defined on all sets. For those
   which are not embeddings of Coq's nats, it defaults to 0. *)

(* inversion property of embedding *)
Lemma FinOrd_embed_inv : forall n m: nat,
  FinOrd_embed n = FinOrd_embed m -> n = m.
Proof. induction n; intros [|m] E; unfold FinOrd_embed in E; simpl; simpl in E.
  reflexivity.
  apply eq_sym in E. destruct (ordS_neq_ordO E).
  destruct (ordS_neq_ordO E).
  apply ordS_inj in E. f_equal. now apply IHn.
Qed.

(* embed and proj form an isomorphism, part 1, id on nat *)
Lemma embed_proj_id : forall n: nat, FinOrd_proj (FinOrd_embed n) = n. 
Proof. intros n. unfold FinOrd_proj.
  destruct (dit {k : nat | iter k ordS ordO = FinOrd_embed n}) as [[k E]|F].
  now apply FinOrd_embed_inv in E.
  exfalso. apply F. now exists n.
Qed.

(* embed and proj form an isomorphism, part 2, id on (suitably subset of) set *)
Lemma proj_embed_id : forall N: set, N :e FinOrd -> FinOrd_embed (FinOrd_proj N) = N.
Proof. intros N N_T. destruct (SepE2 _ _ N_T) as [k E].
  subst N. fold (FinOrd_embed k). rewrite embed_proj_id. reflexivity.
Qed.

(* Some Lemmas about projection *)
Lemma FinOrd_proj_O : FinOrd_proj ordO = 0.
Proof. assert (E: ordO = FinOrd_embed 0) by reflexivity.
  rewrite E. now apply embed_proj_id.
Qed.

Lemma FinOrd_iter_embed : forall n N, iter n ordS ordO = N -> N = FinOrd_embed n.
Proof. intros n N E. unfold FinOrd_embed. congruence. Qed.

Lemma FinOrd_iter_embed_succ : forall n N, N = FinOrd_embed n -> ordS N = FinOrd_embed (S n).
Proof. intros n N E. unfold FinOrd_embed. simpl. f_equal. exact E. Qed.

Lemma FinOrd_proj_S : forall N, N :e FinOrd ->
  FinOrd_proj (ordS N) = S (FinOrd_proj N).
Proof. intros N N_T. destruct (SepE2 _ _ N_T) as [n E].
  apply FinOrd_iter_embed in E.
  rewrite E at 2. rewrite embed_proj_id.
  apply FinOrd_iter_embed_succ in E.
  rewrite E. now rewrite embed_proj_id.
Qed.

Definition FinOrd_rect (z f N: set) : set := 
  nat_rect (fun _ => set) z
    (fun n: nat => fun R: set => ap_a (ap_a f (FinOrd_embed n)) R ) (FinOrd_proj N).

Lemma FinOrd_rec_O : forall z f: set, FinOrd_rect z f ordO = z.
Proof. intros z f. unfold FinOrd_rect. rewrite FinOrd_proj_O. reflexivity. Qed.

Lemma FinOrd_rec_S : forall z f N: set, N :e FinOrd ->
  FinOrd_rect z f (ordS N) = ap_a (ap_a f N) (FinOrd_rect z f N).
Proof. intros z f N H. unfold FinOrd_rect at 1. rewrite (FinOrd_proj_S H). simpl.
  rewrite (proj_embed_id H). reflexivity.
Qed.

Lemma FinOrd_rect_T : forall A: set -> set, forall z f N: set,
  z :e A ordO ->
  f :e Pi_a FinOrd (fun N => (Arr_a (A N) (A (ordS N)))) ->
  N :e FinOrd ->
  FinOrd_rect z f N :e A N.
Proof. intros A z f N z_T f_T N_T. unfold FinOrd_rect.
  (* we need to proof this by induction, but we do not
     have an induction principle for FinOrd, so we
     delegate to nat instead. *)
  rewrite <- (proj_embed_id N_T) at 2.
  generalize (FinOrd_proj N) as k. clear N_T.
  induction k; simpl.
    exact z_T.
    pose proof (ap_a_Pi_a _ f_T (iter_ord_T k)) as g_T. simpl in g_T.
    now apply (ap_a_Arr_a _ g_T IHk).
Qed.

(* Inversions Lemmas for FinOrd, ordO and ordS *)
(* redo with recursion *)
Lemma FinOrdE : forall N, N :e FinOrd ->
  N = ordO \/ exists M, M :e FinOrd /\ N = ordS M.
Proof. intros N N_T.
  apply SepE2 in N_T. destruct N_T as [n E].
  destruct n; simpl in E.
    now left.
    right. exists (iter n ordS ordO). split.
      apply iter_ord_T.
      congruence.
Qed.

Lemma FinOrd_proj_O_inv : forall N, N :e FinOrd -> 0 = FinOrd_proj N -> N = ordO.
Proof. intros N N_T H. destruct (FinOrdE N_T) as [E|[M [M_T E]]].
  exact E.
  subst. rewrite (FinOrd_proj_S M_T) in H. congruence.
Qed.

Lemma FinOrd_proj_S_inv : forall N m, N :e FinOrd -> S m = FinOrd_proj N ->
  exists M: set, M :e FinOrd /\ N = ordS M.
Proof. intros N m N_T H. destruct (FinOrdE N_T) as [E|[M [M_T E]]]; subst.
  rewrite FinOrd_proj_O in H. congruence.
  exists M; now auto.
Qed.




