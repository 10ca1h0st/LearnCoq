From coqlearn Require Export wjm01.

Compute(less 12 14).

Theorem plus_n_0 : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn']. (*can not add "eqn:E"*)
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. simpl. reflexivity.  Qed.

Theorem minus_diag:forall n:nat,n-n=0.
Proof.
intros n.
induction n as [|n' IHn'].
    -(*n=0*)simpl. reflexivity.
    -(*n=S n'*)simpl. rewrite->IHn'. simpl. reflexivity.
Qed.

Theorem mult_0_r:forall n:nat,n*0=0.
Proof.
induction n as [|n' IHn'].
-simpl. reflexivity.
-simpl. rewrite->IHn'. simpl. reflexivity.
Qed.

Theorem plus_n_Sm:forall (n m:nat),S (n+m)=n+(S m).
Proof.
intros n m.
induction n as [|n' IHn'].
    -simpl. reflexivity.
    -simpl. rewrite->IHn'. simpl. reflexivity.
Qed.

Theorem plus_comm:forall (n m:nat),n+m=m+n.
Proof.
intros n m.
induction n as [|n' IHn'].
    -simpl. rewrite<-plus_n_0. simpl. reflexivity.
    -simpl. rewrite<-plus_n_Sm. rewrite->IHn'.
     simpl. reflexivity.
Qed.

Theorem plus_assoc:forall (n m p:nat),n+(m+p)=(n+m)+p.
Proof.
intros n m p.
induction n as [|n' IHn'].
    -simpl. reflexivity.
    -simpl. rewrite->IHn'. simpl. reflexivity.
Qed.

Fixpoint double(n:nat):=
    match n with
        |0=>0
        |S n'=>S (S (double n'))
    end.

Theorem double_plus:forall (n:nat),double n = n+n.
Proof.
induction n as [|n' IHn'].
    -simpl. reflexivity.
    -simpl. rewrite->IHn'. rewrite<-plus_n_Sm.
     simpl. reflexivity.
Qed.

Theorem negb_negb_null:forall n:bool,negb (negb n) = n.
Proof.
intros n.
destruct n eqn:E.
    -simpl. reflexivity.
    -simpl. reflexivity.
Qed.

Theorem evenb_S:forall n:nat,evenb (S n)=negb (evenb n).
Proof.
induction n as [|n' IHn'].
    -simpl. reflexivity.
    -rewrite->IHn'. simpl. rewrite->negb_negb_null.
     simpl. reflexivity.
Qed.

Theorem evenb_S_2:forall n:nat,evenb (S n)=negb (evenb n).
Proof.
intros n.
assert(P: forall x:bool,negb (negb x)=x).
    {
        intros x.
        destruct x.
            -simpl. reflexivity.
            -simpl. reflexivity.
    }
induction n as [|n' IHn'].
    -simpl. reflexivity.
    -rewrite->IHn'. simpl. rewrite->P.
     simpl. reflexivity.
Qed.

(*
Theorem plus_swap:forall (n m p:nat),n+(m+p)=m+(n+p).
Proof.

Qed.
*)




