Require Import TG4.

Theorem NI : forall A: set, forall f: set -> set,
    A :e GU Empty -> (* A in lowest universe *)
    (forall a: set, a :e A -> f a :e A) -> (* f total on A *)
    (forall x y: set, x :e A -> y :e A -> f x = f y -> x = y) -> (* f injective *)
    (forall b: set, b :e A -> exists a: set, a :e A /\ f a = b).  (* f is surjective *)  
  Proof. intros A f A_T tot inj b b_T.
    unfold Type_den, U1.univ in A_T. simpl in A_T. admit. (* TODO *)
  Qed.

  (* Hence we cannot have a infinite member in Type_den 0,
     which in turn means that this version of ECC_M cannot
     validate the existance of infinite types in the lowest
     type universe.
     Therefore (NAT :e Type_den 0) is independent of ECC *)