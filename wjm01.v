
Module NatPlayground.

Inductive nat:Type:=
    |O
    |S (n:nat).

End NatPlayground.

Fixpoint oddn(n:nat):bool:=
    match n with
    |O=>false
    |S O=>true
    |S (S m)=>oddn m
    end.


Fixpoint plus (n m : nat):nat:=
    match n with
        |O => m
        |S n' => S (plus n' m)
    end.

Notation "x + y" := (plus x y).

Fixpoint minus (n m : nat):nat:=
    match n,m with
        |O,_ => O
        |S _,O => n
        |S n',S m' => minus n' m'
    end.
Notation "x - y" := (minus x y).

Fixpoint mult (n m : nat):nat:=
    match n with
        |O => O
        |S n' => (mult n' m)+m
    end.

Notation "x * y" := (mult x y).

Fixpoint exp (base power : nat):nat:=
    match power with
        |O => O
        |S O => base
        |S power' => mult base (exp base power')
    end.

Fixpoint factorial (n : nat):nat:=
    match n with
        |O => 1
        |S n' => mult n (factorial(n'))
    end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Fixpoint less (n m : nat):bool:=
    match n,m with
        |O,O => false
        |O,S m' => true
        |S n',O => false
        |S n',S m' => (less n' m')
    end.

Notation "x <? y" := (less x y) (at level 70) : nat_scope.

Definition less2 (n m : nat):bool:=
    match n,m with
        |O,O => false
        |O,S m' => true
        |S n',O => false
        |_,_ => match n-m with
                    |O => match m-n with
                              |O => false
                              |_ => true
                          end
                    |_ => false
                end
    end.
Compute (less2 28 27).

Example test_example:1+2=3.
Proof. Admitted.

Theorem plus_0_n:forall n:nat,0+n=n.
Proof. intros n. simpl. reflexivity. Qed.

Example plus_reverse:forall n m:nat,m=n->n+m=m+n.
Proof. 
intros n m. intros G. rewrite <- G.
simpl. reflexivity. Qed.

Theorem plus_id_exercise:forall n m o:nat,
    n=m -> m=o -> n+m=m+o.
Proof.
intros n m o. intros H I. rewrite -> H. rewrite <- I.
simpl. reflexivity. Qed.

Theorem t1:forall n m:nat,(0+n)*m = n*m.
Proof.
intros n m. rewrite -> plus_0_n.
simpl. reflexivity. Qed.


Theorem pre:forall n:nat,S n = 1+n.
Proof. simpl. reflexivity. Qed.


Theorem mult_S_l:forall n m:nat,m=S n->m*(1+n)=m*m.
Proof.
intros n m. intros H. rewrite <- pre. rewrite <- H.
simpl. reflexivity. Qed.


Theorem plus_one_high_zero:forall n m:nat,0<?n+m+1=true.
Proof. intros n m. destruct n as [|n'] eqn:En.
-destruct m as [|n''] eqn:Em.
    +simpl. reflexivity.
    +simpl. reflexivity.
-destruct m as [|n''] eqn:Em.
    +simpl. reflexivity.
    +simpl. reflexivity.
Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_true_elim2:forall b c:bool,andb b c=true->c=true.
Proof. intros b c H.
destruct b eqn:Eb.
-rewrite <- H. simpl. reflexivity.
-destruct c eqn:Ec.
    { simpl. reflexivity. }
    { rewrite <- H. simpl. reflexivity. }
Qed.

Theorem zero_nbeq_plus_1:forall n:nat,(0=?(n+1))=false.
Proof. intros n.
destruct n eqn:E.
-simpl. reflexivity.
-simpl. reflexivity.
Qed.


Theorem identity_fn_applied_twice:
forall (f:bool->bool),
(forall (x:bool),f x=x)->forall (b:bool),f(f b)=b.
Proof.
intros f H b.
rewrite -> H.
rewrite -> H.
simpl. reflexivity.
Qed.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Theorem negation_fn_applied_twice:
forall (f:bool->bool),
(forall (x:bool),f x=negb x)->forall (b:bool),f(f b)=b.
Proof.
intros f H b.
destruct b eqn:Eb.
-rewrite -> H. rewrite -> H. simpl. reflexivity.
-rewrite -> H. rewrite -> H. simpl. reflexivity.
Qed.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Theorem andb_true_c_eq_c:forall c:bool,andb true c=c.
Proof. simpl. reflexivity. Qed.

Theorem orb_true_c_eq_true:forall c:bool,orb true c=true.
Proof. simpl. reflexivity. Qed.

Theorem andb_false_c_eq_false:forall c:bool,andb false c=false.
Proof. simpl. reflexivity. Qed.

Theorem orb_false_c_eq_c:forall c:bool,orb false c=c.
Proof. simpl. reflexivity. Qed.


Theorem andb_eq_orb:
forall (b c:bool),andb b c=orb b c->b=c.
Proof.
intros b c.
destruct b eqn:Eb.
-rewrite -> andb_true_c_eq_c. rewrite->orb_true_c_eq_true.
intros H. rewrite->H. simpl. reflexivity.
-rewrite->andb_false_c_eq_false. rewrite->orb_false_c_eq_c.
intros H. rewrite->H. simpl. reflexivity.
Qed.
