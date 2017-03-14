(*** specifying and extending the used metatheory ***)

(*** Classical + Extensional + Choice ***)
(* Require Export Coq.Logic.ClassicalFacts. *)
Require Export Coq.Logic.Classical_Prop.
(* Require Export Coq.Logic.FunctionalExtensionality. *)
Require Export Coq.Logic.Epsilon.

(* Since we are classical and have choice, we have
   an informative version of excluded middle as well
   as a decision procedure for the inhabitance of
   types.
 *)

Definition IXM : Type := forall P:Prop, P + ~P.
Definition DIT : Type := forall T:Type, T + (T -> False).

Theorem ixm : IXM.
Proof. unfold IXM. intros P.
  assert (I: inhabited (P + ~P)). destruct (classic P).
    constructor. left. exact H.
    constructor. right. exact H.
  apply (@epsilon (P + (~P)) I (fun _ => True)).
Qed.

Theorem dit : DIT.
Proof. unfold DIT. intros T.
  destruct (ixm (inhabited T)) as [H|H].
  left. apply (epsilon H (fun _ => True)).
  right. intros t. apply H. constructor. exact t.
Qed.

(*** Some convenient tools ***)
Fixpoint iter (n:nat) {X:Type} (f: X -> X) (x: X) := match n with
  | O => x
  | S n' => f (iter n' f x)
end.